package de.dfki.lt.loot.tfs.io;

import java.io.IOException;
import java.util.Arrays;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


public class TableOfContents {

  private static final Logger LOGGER =
    LoggerFactory.getLogger(TableOfContents.class);

  /** Sections in the binary dump files for different types of information:
   *  - symbol table
   *  - print names
   *  - type hierarchy
   *  - feature tables         (fixed arity encoding), not used at the moment
   *  - full forms             simple replacement for lexicon, not used
   *  - inflectional rules     not used
   *  - type constraints       the feature structures
   *  - irregular morphological entries
   *  - direct supertype table
   *  - chart dump section (chart edges with feature structures)
   */
  public enum Section {
    NOSECTION, SYMTAB, PRINTNAMES, HIERARCHY,
    FEATTABS, FULLFORMS, INFLR, CONSTRAINTS,
    IRREGS, PROPERTIES, SUPERTYPES, CHART
  }

  private PetUndumper _u;

  private String _grammarDescription;

  // table of content to determine the offsets to the different sections
  private int[] _sectionOffsets;

  /** Dump/Undump the header of the grammar file.
   * It consists of the magic number, the dumper version and the \a description,
   * which should be a string describing the grammar and grammar version.
   * @throws IOException
   */
  private String undumpHeader(PetUndumper u) throws IOException {
    // magic number to identify file format
    int magicNumber = u.undumpInt();
    if (magicNumber != 0x03422711) {
      throw new IOException("Wrong grammar magic number, not a PET grammar");
    }

    // grammar format version
    int grammarFormat = u.undumpInt();
    if (grammarFormat < 17) {
      throw new IOException("Wrong grammar format " + grammarFormat
          + ", unable to read");
    }

    // grammar info
    return u.undumpString();
  }

  /** Extract the table of contents from the dumper, which is a list of
   *  file offsets for the known sections (see Sections enum).
   */
  private int[] undumpToc(PetUndumper u) {
    int[] sectionOffsets = new int[Section.values().length];
    Arrays.fill(sectionOffsets, -1);
    int sectionType;
    // 0 indicates the end of TOC
    while ((sectionType = u.undumpInt()) != 0) {
      // don't know if section types come in ascending order
      if (sectionType > 0 && sectionType < Section.values().length) {
        sectionOffsets[sectionType] = u.undumpInt();
      } else {
        LOGGER.warn("unknown section type: " + sectionType);
        u.undumpInt();
        break;
      }
    }
    return sectionOffsets;
  }

  /** Read the table of contents from the grammar file, which makes it possible
   *  to jump to the different sections to extract the different kinds of
   *  data structures.
   */
  public TableOfContents(PetUndumper u) throws IOException {
    _u = u;
    _u.seekAbsolute(0);
    _grammarDescription = undumpHeader(u);
    _sectionOffsets = undumpToc(u);
  }

  public void gotoSection(Section s) throws IOException {
    _u.seekAbsolute(_sectionOffsets[s.ordinal()]);
    int sectionType = _u.undumpInt(); // read section type
    if (sectionType != s.ordinal())
      throw new IOException("Section does not start with appropriate " +
          "section identifier: " + sectionType +
          " instead of " + s.ordinal());
  }

  /** Get the grammar description read from the header */
  String grammarDescription() {
    return _grammarDescription;
  }
}
