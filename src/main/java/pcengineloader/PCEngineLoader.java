/* ###
 * IP: GHIDRA
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 *      http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package pcengineloader;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import docking.widgets.OptionDialog;
import ghidra.app.util.Option;
import ghidra.app.util.OptionUtils;
import ghidra.app.util.bin.BinaryReader;
import ghidra.app.util.bin.ByteProvider;
import ghidra.app.util.bin.ByteProviderInputStream;
import ghidra.app.util.importer.MessageLog;
import ghidra.app.util.opinion.AbstractLibrarySupportLoader;
import ghidra.app.util.opinion.LoadSpec;
import ghidra.program.flatapi.FlatProgramAPI;
import ghidra.program.model.address.Address;
import ghidra.program.model.lang.LanguageCompilerSpecPair;
import ghidra.program.model.listing.Program;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.util.AddressLabelInfo;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.InvalidInputException;
import ghidra.util.task.TaskMonitor;

/*
 * Loads banks and creates functions for interrupt vectors.
 * 
 * References:
 * - https://www.chibiakumas.com/6502/pcengine.php
 * - http://www.magicengine.com/mkit/doc_hard_cpu.html
 * - http://shu.sheldows.com/shu/download/pcedocs/pce_memory.html
 */
public class PCEngineLoader extends AbstractLibrarySupportLoader {

	private static final int MAX_PAGES = 8;
	private static final int MAX_BANKS = 0x80; // ROM size = 1MB

	private boolean isROM = true;
	
	@Override
	public String getName() {
		return "PC-Engine / TurboGrafx-16";
	}

	@Override
	public Collection<LoadSpec> findSupportedLoadSpecs(ByteProvider provider) throws IOException {
		List<LoadSpec> loadSpecs = new ArrayList<>();

		// Too small to contain interrupt vectors.
		if (provider.length() < 0x2000) {
			return loadSpecs;
		}

		// Heuristic 1: Using ROM bank loading subroutine snippet as magic byte sequence:
		//
		// LDA $FF ; a9ff
		// TAM $01 ; 5301
		// LDA $F8 ; a9f8
		// TAM $02 ; 5302
		ByteProviderInputStream in = (ByteProviderInputStream) provider.getInputStream(0);
		byte[] bytes = in.readAllBytes();
		Pattern magic = Pattern.compile("\\xa9\\xff\\x53\\x01\\xa9\\xf8\\x53\\x02");
		Matcher matcher = magic.matcher(new ByteCharSequence(bytes));
		boolean is_pce = matcher.find();

		// Heuristic 2: Check interrupt vectors at 0x1ff6, preceded by 0xff bytes.
		//
		// We assume that each vector is in MPR7's address range, which covers more cases
		// with hopefully few false positives...
		is_pce |= findIntVecs(provider, 0x1FF0);
		if (provider.length() == 0x10000) {
			// Check paged offset on RAM dump image.
			is_pce |= findIntVecs(provider, 0xFFF0);
		}

		if (is_pce) {
			if (provider.length() == 0x10000) {
				int choice =
						OptionDialog.showOptionNoCancelDialog(
						null,
						"Choose image type",
						"<html>Detected PC-Engine image with length=0x10000, is this a ROM or a RAM dump?<br>Pages are assigned automatically for RAM dumps.",
						"ROM",
						"RAM",
					OptionDialog.QUESTION_MESSAGE);
				if (choice == OptionDialog.OPTION_TWO) {
					isROM = false;
				}
			}
			
			loadSpecs.add(new LoadSpec(this, 0, new LanguageCompilerSpecPair("HuC6280:LE:16:default", "default"), true));
		}

		return loadSpecs;
	}

	private boolean findIntVecs(ByteProvider provider, int offset) throws IOException {
		boolean is_pce = true;
		BinaryReader reader = new BinaryReader(provider, true);
		
		for (int i = offset; i < offset + 6; i += 2) {
			int v = reader.readUnsignedShort(i);
			if (v != 0xffff) {
				is_pce = false;
				break;
			}
		}
		for (int i = offset + 6; i < offset + 0x10; i += 2) {
			int v = reader.readUnsignedShort(i);
			if (v < 0xe000 || v > 0xfff0) {
				is_pce = false;
				break;
			}
		}
		
		return is_pce;
	}

	@Override
	protected void load(ByteProvider provider, LoadSpec loadSpec, List<Option> options,
			Program program, TaskMonitor monitor, MessageLog log)
			throws CancelledException, IOException {
		final BinaryReader reader = new BinaryReader(provider, true);
		final FlatProgramAPI fpa = new FlatProgramAPI(program, monitor);

		/*
		 * page    0: bank $FF (I/O)
		 * page    1: bank $F8 (RAM)
		 * page 2..6: user definable
		 * page    7: bank $00
		 */
		final long bank_size = 0x2000L;
		final InputStream romStream = provider.getInputStream(0);
		if (isROM) {
			createSegment(fpa, null, "MPR0_IO",    0x0000, bank_size, true, true, false, true, false, log);
			createSegment(fpa, null, "MPR1_ZPRAM", 0x2000, 0x100, true, true, false, true, false, log);
			createSegment(fpa, null, "MPR1_STACK", 0x2100, 0x100, true, true, false, true, false, log);
			createSegment(fpa, null, "MPR1_WRAM",  0x2200, 0x1e00, true, true, false, true, false, log);
			createSegment(fpa, provider.getInputStream(0), "MPR7_ROM", (bank_size * 7), bank_size, true, false, true, false, false, log);

			// Note that each ROM bank should be manually added to the program,
			// with base address matching the page assigned in the user program (look for LDA + TAM instructions).
			// Here we just overlay all banks in page 2.
			final long page2_offset = bank_size * 2;
			for (int i = 0; i < MAX_BANKS; i++) {
				createSegment(fpa, provider.getInputStream(Math.min(romStream.available(), bank_size * i)),
						"Bank" + String.format("%02X", i), page2_offset, bank_size, true, false, true, false, true, log);
				if (romStream.available() < bank_size * (i + 1)) {
					break;
				}
			}
		} else {
			createSegment(fpa, provider.getInputStream(0x0000), "MPR0_IO",    0x0000, bank_size, true, true, false, true, false, log);
			createSegment(fpa, provider.getInputStream(0x2000), "MPR1_ZPRAM", 0x2000, 0x100, true, true, false, true, false, log);
			createSegment(fpa, provider.getInputStream(0x2100), "MPR1_STACK", 0x2100, 0x100, true, true, false, true, false, log);
			createSegment(fpa, provider.getInputStream(0x2200), "MPR1_WRAM",  0x2200, 0x1e00, true, true, false, true, false, log);
			
			for (int i = 2; i < MAX_PAGES; i++) {
				createSegment(fpa, provider.getInputStream(bank_size * i),
						"MPR" + i, bank_size * i, bank_size, true, false, true, false, false, log);
			}
		}

		// Ensure function "Reset" is the first to be created, 
		// since interrupt vectors might default to it.
		Map<Long, String> intVecs = new TreeMap<Long, String>(Collections.reverseOrder());
		intVecs.putAll(Map.of(
				0x1FF6L, "IRQ2_BRK",
				0x1FF8L, "IRQ1_VDC",
				0x1FFAL, "Timer",
				0x1FFCL, "NMI",
				0x1FFEL, "Reset"
				));
		for (Map.Entry<Long, String> entry : intVecs.entrySet()) {
			final long offset = isROM ? entry.getKey() : entry.getKey() + 0xE000L;
			final String name = entry.getValue();
			reader.setPointerIndex(offset);
			final Address address = fpa.toAddr(reader.readNextUnsignedShort());
			fpa.createFunction(address, name);
			if (name.equalsIgnoreCase("Reset")) {
				fpa.addEntryPoint(address);
			}
		}

		// Always use language defined labels, regardless of APPLY_LABELS_OPTION_NAME.
		List<AddressLabelInfo> labels = loadSpec.getLanguageCompilerSpec().getLanguage().getDefaultSymbols();
		for (AddressLabelInfo info : labels) {
			try {
				// TODO: Add CD labels for CD images.
				final long offset = info.getAddress().getUnsignedOffset();
				if (offset >= 0x1800) {
					continue;
				}
				program.getSymbolTable().createLabel(info.getAddress(), info.getLabel(), SourceType.IMPORTED);
			} catch (InvalidInputException e) {
				log.appendException(e);
			}
		}

		monitor.setMessage(String.format("%s : Loading done", getName()));
	}

	private void createSegment(FlatProgramAPI fpa,
			InputStream stream,
			String name,
			long address,
			long size,
			boolean read,
			boolean write,
			boolean execute,
			boolean volatil,
			boolean overlay,
			MessageLog log) {
		MemoryBlock block;
		try {
			block = fpa.createMemoryBlock(name, fpa.toAddr(address), stream, size, overlay);
			block.setRead(read);
			block.setWrite(write);
			block.setExecute(execute);
			block.setVolatile(volatil);
		} catch (Exception e) {
			log.appendException(e);
		}
	}

	public class ByteCharSequence implements CharSequence {

		private final byte[] data;
		private final int length;
		private final int offset;

		public ByteCharSequence(byte[] data) {
			this(data, 0, data.length);
		}

		public ByteCharSequence(byte[] data, int offset, int length) {
			this.data = data;
			this.offset = offset;
			this.length = length;
		}

		@Override
		public int length() {
			return this.length;
		}

		@Override
		public char charAt(int index) {
			return (char) (data[offset + index] & 0xff);
		}

		@Override
		public CharSequence subSequence(int start, int end) {
			return new ByteCharSequence(data, offset + start, end - start);
		}
	}
}
