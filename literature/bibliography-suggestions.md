# Suggested bibliography additions

Review date: 23 October 2026.

This checklist records the suggestions from the review of the files included by `main.tex`. The proposed entries have **not** been added to `bib.bib`, and the book text has not been edited. BibTeX follows the existing bibliography's style: descriptive keys, family-name-first authors, TeX accents, braced values, aligned fields, and DOI links.

Each proposal includes a paste-ready BibTeX entry, a suggested location, and a short LaTeX sentence in the style of the book's bibliographical notes. The sentences are editorial suggestions; precise theorem/page pinpoints should be added only after checking the relevant version.

## PDF collection

13 full PDFs have been placed in `literature/pdfs/`, following the existing `AuthorNamesYear_Title_With_Underscores.pdf` convention. Version suffixes distinguish preprints and non-final drafts. Each file was opened by `pdfinfo` and its title/author information checked with text extraction or visual inspection. Sources and version caveats are recorded below. The three proposals without a verified full PDF are Simon (1990), Choffrut (2003), and Nekrashevych (2005).

The repository ignores PDFs in Git; the downloaded files are available locally even though they do not appear as ordinary untracked files. Existing PDFs have not been replaced. Mohri's author-hosted PostScript was converted locally to PDF.

## New entries

### 1. Factorization forests of finite height (1990)

**Suggested location:** Part D, `evaluation.tex`, Theorem `thm:factorisation-forest`; Part D references.

The original source of the factorisation forest theorem used throughout evaluation and MSO interpretations.

**PDF status:** No verified full PDF obtained. The publisher download returned HTTP 403; searches found related Simon papers, which have not been substituted for this paper.

```bibtex
@article{simon1990,
  author  = {Simon, Imre},
  title   = {Factorization forests of finite height},
  journal = {Theoretical Computer Science},
  volume  = {72},
  number  = {1},
  pages   = {65--94},
  year    = {1990},
  doi     = {10.1016/0304-3975(90)90047-L},
  url     = {https://doi.org/10.1016/0304-3975(90)90047-L}
}
```

Suggested bibliographical-note text:

```latex
The Factorisation Forest Theorem is due to Simon~\cite{simon1990}.
```

### 2. On factorisation forests (2007)

**Suggested location:** Part D, Simon trees and the construction of factorisations.

Related developments, including deterministic variants. Listed as the verified arXiv manuscript rather than assigning unverified conference metadata.

**PDF:** [Colcombet2007_On_Factorisation_Forests_preprint.pdf](pdfs/Colcombet2007_On_Factorisation_Forests_preprint.pdf). arXiv:cs/0701113v1, 17 January 2007.

**Download source:** [Full-text source](https://arxiv.org/pdf/cs/0701113).

```bibtex
@article{colcombet2007,
  author  = {Colcombet, Thomas},
  title   = {On factorisation forests},
  journal = {CoRR},
  year    = {2007},
  doi     = {10.48550/arXiv.cs/0701113},
  url     = {https://arxiv.org/abs/cs/0701113}
}
```

Suggested bibliographical-note text:

```latex
For extensions and deterministic variants, see~\cite{colcombet2007}.
```

### 3. The factorisation forest theorem (2021)

**Suggested location:** Part D references, after the original Simon attribution.

A systematic further-reading reference on factorisation forests and their variants.

**PDF:** [Colcombet2021_The_Factorisation_Forest_Theorem_non-final_draft.pdf](pdfs/Colcombet2021_The_Factorisation_Forest_Theorem_non-final_draft.pdf). Author-hosted non-final draft dated 23 August 2012, not the final 2021 chapter. Published pagination must not be used to locate passages in this draft.

**Download source:** [Full-text source](https://www.irif.fr/~colcombe/Publications/handbook-fft-colcombet_non-final.pdf).

```bibtex
@incollection{colcombet2021,
  author    = {Colcombet, Thomas},
  title     = {The factorisation forest theorem},
  booktitle = {Handbook of Automata Theory, Volume I},
  editor    = {Pin, Jean-{\'E}ric},
  pages     = {653--693},
  publisher = {EMS Press},
  year      = {2021},
  note      = {An early non-final author draft, dated 23 August 2012, is available separately; it is not the final published chapter},
  doi       = {10.4171/AUTOMATA-1/18},
  url       = {https://doi.org/10.4171/AUTOMATA-1/18}
}
```

Suggested bibliographical-note text:

```latex
A detailed account of factorisation forests and their applications can be found in~\cite{colcombet2021}.
```

### 4. Transducers on Compressed Strings (2026)

**Suggested location:** Part B, `exer:rational-compression`; Part C, `exer:regular-compression`; Part D, `exer:polyregular-marked-squaring-compression` and `exer:polyregular-unmarked-squaring`.

Directly relevant to the compression exercises, including closure under map lifting and the separation using marked squaring.

**PDF:** [BojanczykLohrey2026_Transducers_on_Compressed_Strings.pdf](pdfs/BojanczykLohrey2026_Transducers_on_Compressed_Strings.pdf). Published ICALP 2026 paper.

**Download source:** [Full-text source](https://drops.dagstuhl.de/storage/00lipics/lipics-vol374-icalp2026/LIPIcs.ICALP.2026.170/LIPIcs.ICALP.2026.170.pdf).

```bibtex
@inproceedings{bojanczykLohrey2026,
  author    = {Boja{\'n}czyk, Miko{\l}aj and Lohrey, Markus},
  title     = {Transducers on Compressed Strings},
  booktitle = {ICALP 2026},
  pages     = {170:1--170:22},
  year      = {2026},
  doi       = {10.4230/LIPIcs.ICALP.2026.170},
  url       = {https://doi.org/10.4230/LIPIcs.ICALP.2026.170}
}
```

Suggested bibliographical-note text:

```latex
The results about compatibility with grammar compression are from~\cite{bojanczykLohrey2026}.
```

### 5. First-order Definable String Transformations (2014)

**Suggested location:** Part C, `sec:logic-aperiodic`, and Part C references.

The SST characterisation of first-order definable transformations; complements the language-level historical references already cited.

**PDF:** [FiliotKrishnaTrivedi2014_First-Order_Definable_String_Transformations.pdf](pdfs/FiliotKrishnaTrivedi2014_First-Order_Definable_String_Transformations.pdf). Published FSTTCS 2014 paper.

**Download source:** [Full-text source](https://drops.dagstuhl.de/storage/00lipics/lipics-vol029-fsttcs2014/LIPIcs.FSTTCS.2014.147/LIPIcs.FSTTCS.2014.147.pdf).

```bibtex
@inproceedings{filiotKrishnaTrivedi2014,
  author    = {Filiot, Emmanuel and Krishna, Shankara Narayanan and Trivedi, Ashutosh},
  title     = {First-order Definable String Transformations},
  booktitle = {FSTTCS 2014},
  pages     = {147--159},
  year      = {2014},
  doi       = {10.4230/LIPIcs.FSTTCS.2014.147},
  url       = {https://doi.org/10.4230/LIPIcs.FSTTCS.2014.147}
}
```

Suggested bibliographical-note text:

```latex
For a characterisation of first-order string transformations using streaming string transducers, see~\cite{filiotKrishnaTrivedi2014}.
```

### 6. Aperiodic Two-way Transducers and FO-Transductions (2015)

**Suggested location:** Part C, paragraph on first-order definable regular functions at the end of `sec:logic-aperiodic`.

The corresponding characterisation using aperiodic two-way transducers. Keep the list-functions reference for the book's exact prime decomposition.

**PDF:** [CartonDartois2015_Aperiodic_Two-Way_Transducers_and_FO-Transductions.pdf](pdfs/CartonDartois2015_Aperiodic_Two-Way_Transducers_and_FO-Transductions.pdf). Published CSL 2015 paper.

**Download source:** [Full-text source](https://drops.dagstuhl.de/storage/00lipics/lipics-vol041-csl2015/LIPIcs.CSL.2015.160/LIPIcs.CSL.2015.160.pdf).

```bibtex
@inproceedings{cartonDartois2015,
  author    = {Carton, Olivier and Dartois, Luc},
  title     = {Aperiodic Two-way Transducers and {FO}-Transductions},
  booktitle = {CSL 2015},
  pages     = {160--174},
  year      = {2015},
  doi       = {10.4230/LIPIcs.CSL.2015.160},
  url       = {https://doi.org/10.4230/LIPIcs.CSL.2015.160}
}
```

Suggested bibliographical-note text:

```latex
The characterisation of first-order transductions by aperiodic two-way transducers is from~\cite{cartonDartois2015}.
```

### 7. Continuity of Functional Transducers: A Profinite Study of Rational Functions (2020)

**Suggested location:** Introduction, continuity and the profinite metric; Part B references.

A direct connection to the book's continuity criterion, with finer preservation questions for classes of regular languages.

**PDF:** [CadilhacCartonPaperman2020_Continuity_of_Functional_Transducers_A_Profinite_Study_of_Rational_Functions.pdf](pdfs/CadilhacCartonPaperman2020_Continuity_of_Functional_Transducers_A_Profinite_Study_of_Rational_Functions.pdf). Published LMCS article.

**Download source:** [Full-text source](https://lmcs.episciences.org/6132/pdf).

```bibtex
@article{cadilhacCartonPaperman2020,
  author  = {Cadilhac, Micha{\"e}l and Carton, Olivier and Paperman, Charles},
  title   = {Continuity of Functional Transducers: A Profinite Study of Rational Functions},
  journal = {Logical Methods in Computer Science},
  volume  = {16},
  number  = {1},
  pages   = {24:1--24:29},
  year    = {2020},
  doi     = {10.23638/LMCS-16(1:24)2020},
  url     = {https://doi.org/10.23638/LMCS-16(1:24)2020}
}
```

Suggested bibliographical-note text:

```latex
Continuity of rational functions, including preservation of particular classes of regular languages, is studied in~\cite{cadilhacCartonPaperman2020}.
```

### 8. Minimizing subsequential transducers: a survey (2003)

**Suggested location:** Part B, machine-independent characterisations and the subsequential minimisation exercises.

Accessible supplementary reading on minimisation and output normalisation; retain the original 1977 attribution.

**PDF status:** No verified full PDF obtained. The publisher download returned HTTP 403; no working university-hosted full copy was located.

```bibtex
@article{choffrut2003,
  author  = {Choffrut, Christian},
  title   = {Minimizing subsequential transducers: a survey},
  journal = {Theoretical Computer Science},
  volume  = {292},
  number  = {1},
  pages   = {131--143},
  year    = {2003},
  doi     = {10.1016/S0304-3975(01)00219-5},
  url     = {https://doi.org/10.1016/S0304-3975(01)00219-5}
}
```

Suggested bibliographical-note text:

```latex
For a survey of subsequential transducer minimisation, see~\cite{choffrut2003}.
```

### 9. Enumeration of monadic second-order queries on trees (2013)

**Suggested location:** Part D, `sec:evaluation-algorithm` and Part D references.

Related work on linear preprocessing and constant-delay enumeration using factorisation forests. This is background, not by itself a source for enumeration in the interpretation's output order.

**PDF:** [KazanaSegoufin2013_Enumeration_of_Monadic_Second-Order_Queries_on_Trees_preprint.pdf](pdfs/KazanaSegoufin2013_Enumeration_of_Monadic_Second-Order_Queries_on_Trees_preprint.pdf). University-hosted author manuscript, 12 pages; its first page has placeholder volume/DOI metadata. The BibTeX describes the published article.

**Download source:** [Full-text source](https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/KS-tocl13.pdf).

```bibtex
@article{kazanaSegoufin2013,
  author  = {Kazana, Wojciech and Segoufin, Luc},
  title   = {Enumeration of monadic second-order queries on trees},
  journal = {ACM Transactions on Computational Logic},
  volume  = {14},
  number  = {4},
  pages   = {25:1--25:12},
  year    = {2013},
  doi     = {10.1145/2528928},
  url     = {https://doi.org/10.1145/2528928}
}
```

Suggested bibliographical-note text:

```latex
Related applications of factorisation forests to query enumeration can be found in~\cite{kazanaSegoufin2013}.
```

### 10. Characterizing Regular Languages with Polynomial Densities (1992)

**Suggested location:** Part A, `exer:polynomial-image-growth-decidable`; Part B, the exercises on ideals classified by range growth.

A source for the polynomial-density structure of regular languages. Distinguish exact-length counts from the book's cumulative length-at-most counts.

**PDF:** [SzilardYuZhangShallit1992_Characterizing_Regular_Languages_with_Polynomial_Densities.pdf](pdfs/SzilardYuZhangShallit1992_Characterizing_Regular_Languages_with_Polynomial_Densities.pdf). Full published chapter, 10 pages. Publication year is 1992; the publisher's later online date is not the conference year.

**Download source:** [Full-text source](https://link.springer.com/content/pdf/10.1007/3-540-55808-X_48.pdf).

```bibtex
@inproceedings{szilardYuZhangShallit1992,
  author    = {Szilard, Andrew and Yu, Sheng and Zhang, Kaizhong and Shallit, Jeffrey},
  title     = {Characterizing Regular Languages with Polynomial Densities},
  booktitle = {MFCS 1992},
  series    = {Lecture Notes in Computer Science},
  volume    = {629},
  pages     = {494--503},
  publisher = {Springer},
  year      = {1992},
  doi       = {10.1007/3-540-55808-X_48},
  url       = {https://doi.org/10.1007/3-540-55808-X_48}
}
```

Suggested bibliographical-note text:

```latex
The structure of regular languages of polynomial density is studied in~\cite{szilardYuZhangShallit1992}.
```

### 11. Self-Similar Groups (2005)

**Suggested location:** Part A, `exer:invertible-mealy-group`.

Optional further reading on automata groups, extending the adding-machine example.

**PDF status:** No verified full book PDF obtained. The publisher download returned HTTP 403; no replacement paper or partial chapter has been stored as the book.

```bibtex
@book{nekrashevych2005,
  author    = {Nekrashevych, Volodymyr},
  title     = {Self-Similar Groups},
  series    = {Mathematical Surveys and Monographs},
  volume    = {117},
  publisher = {American Mathematical Society},
  year      = {2005},
  doi       = {10.1090/surv/117},
  url       = {https://doi.org/10.1090/surv/117}
}
```

Suggested bibliographical-note text:

```latex
For the theory of groups generated by invertible Mealy machines, see~\cite{nekrashevych2005}.
```

### 12. Types, Abstraction and Parametric Polymorphism (1983)

**Suggested location:** Part D, `lem:fundamental-lemma`, as methodological background.

Background on logical relations and parametricity, rather than attribution of the particular polyregular completeness proof.

**PDF:** [Reynolds1983_Types_Abstraction_and_Parametric_Polymorphism.pdf](pdfs/Reynolds1983_Types_Abstraction_and_Parametric_Polymorphism.pdf). Scanned proceedings paper, 11 pages. Title, author, year and first printed page checked visually.

**Download source:** [Full-text source](https://www.cs.cmu.edu/~crary/819-f09/Reynolds83.pdf).

```bibtex
@inproceedings{reynolds1983,
  author    = {Reynolds, John C.},
  title     = {Types, Abstraction and Parametric Polymorphism},
  booktitle = {Information Processing 83},
  editor    = {Mason, R. E. A.},
  pages     = {513--523},
  publisher = {North-Holland},
  year      = {1983},
  url       = {https://www.cs.cmu.edu/~crary/819-f09/Reynolds83.pdf}
}
```

Suggested bibliographical-note text:

```latex
For background on logical relations and parametricity, see~\cite{reynolds1983}.
```

### 13. Theorems for free! (1989)

**Suggested location:** Part C, natural-transformation exercises; Part D, higher-order terms.

Accessible background on deriving uniformity properties from polymorphic types. Naturality and relational parametricity should not be identified without qualification.

**PDF:** [Wadler1989_Theorems_for_Free_preprint.pdf](pdfs/Wadler1989_Theorems_for_Free_preprint.pdf). University-hosted June 1989 manuscript, 13 pages; the first-page note identifies it as a slightly revised version of the FPCA 1989 paper.

**Download source:** [Full-text source](https://home.ttic.edu/~dreyer/course/papers/wadler.pdf).

```bibtex
@inproceedings{wadler1989,
  author    = {Wadler, Philip},
  title     = {Theorems for free!},
  booktitle = {FPCA 1989},
  pages     = {347--359},
  publisher = {ACM},
  year      = {1989},
  doi       = {10.1145/99370.99404},
  url       = {https://doi.org/10.1145/99370.99404}
}
```

Suggested bibliographical-note text:

```latex
A related perspective on uniformity in polymorphic functions is presented in~\cite{wadler1989}.
```

### 14. Minimization algorithms for sequential transducers (2000)

**Suggested location:** Part B, subsequential minimisation; optional supplement to Choffrut's survey.

An algorithmic reference for minimising sequential transducers.

**PDF:** [Mohri2000_Minimization_Algorithms_for_Sequential_Transducers.pdf](pdfs/Mohri2000_Minimization_Algorithms_for_Sequential_Transducers.pdf). Published journal paper, 25 pages, converted locally to PDF from the author's PostScript file.

**Download source:** [Author-hosted PostScript](https://cs.nyu.edu/~mohri/pub/tcs.ps).

```bibtex
@article{mohri2000,
  author  = {Mohri, Mehryar},
  title   = {Minimization algorithms for sequential transducers},
  journal = {Theoretical Computer Science},
  volume  = {234},
  number  = {1--2},
  pages   = {177--201},
  year    = {2000},
  doi     = {10.1016/S0304-3975(98)00115-7},
  url     = {https://doi.org/10.1016/S0304-3975(98)00115-7}
}
```

Suggested bibliographical-note text:

```latex
Algorithms for minimising sequential transducers are described in~\cite{mohri2000}.
```

### 15. Polyregular Functions on Unordered Trees of Bounded Height (2024) — optional outlook

**Suggested location:** Optional outlook in Part D, beside the discussion of equivalence.

A decidable equivalence result for an adjacent setting of unordered bounded-height trees. It does not settle the string-to-string equivalence problem.

**PDF:** [BojanczykKlin2024_Polyregular_Functions_on_Unordered_Trees_of_Bounded_Height.pdf](pdfs/BojanczykKlin2024_Polyregular_Functions_on_Unordered_Trees_of_Bounded_Height.pdf). Author-hosted article with published POPL 2024 metadata, 26 pages.

**Download source:** [Full-text source](https://www.cs.ox.ac.uk/people/bartek.klin/papers/popl24.pdf).

```bibtex
@article{bojanczykKlin2024,
  author  = {Boja{\'n}czyk, Miko{\l}aj and Klin, Bartek},
  title   = {Polyregular Functions on Unordered Trees of Bounded Height},
  journal = {Proceedings of the ACM on Programming Languages},
  volume  = {8},
  number  = {POPL},
  pages   = {45:1--45:26},
  year    = {2024},
  doi     = {10.1145/3632887},
  url     = {https://doi.org/10.1145/3632887}
}
```

Suggested bibliographical-note text:

```latex
For an equivalence result in the related setting of unordered trees of bounded height, see~\cite{bojanczykKlin2024}.
```

### 16. Expregular Functions (2026) — optional outlook

**Suggested location:** Optional outlook in the introduction, on models beyond the transducer ladder.

Further reading on a robust class beyond polynomial growth; not a missing attribution for an existing proof.

**PDF:** [ColcombetLhoteOhlmann2026_Expregular_Functions.pdf](pdfs/ColcombetLhoteOhlmann2026_Expregular_Functions.pdf). Published ICALP 2026 paper.

**Download source:** [Full-text source](https://drops.dagstuhl.de/storage/00lipics/lipics-vol374-icalp2026/LIPIcs.ICALP.2026.176/LIPIcs.ICALP.2026.176.pdf).

```bibtex
@inproceedings{colcombetLhoteOhlmann2026,
  author    = {Colcombet, Thomas and Lhote, Nathan and Ohlmann, Pierre},
  title     = {Expregular Functions},
  booktitle = {ICALP 2026},
  pages     = {176:1--176:15},
  year      = {2026},
  doi       = {10.4230/LIPIcs.ICALP.2026.176},
  url       = {https://doi.org/10.4230/LIPIcs.ICALP.2026.176}
}
```

Suggested bibliographical-note text:

```latex
For a class of transformations beyond polynomial growth, see the expregular functions of~\cite{colcombetLhoteOhlmann2026}.
```

## Existing entries needing citation placement

These ten entries already occur in `bib.bib`. Their BibTeX blocks are reproduced unchanged for convenience: **do not paste them into `bib.bib` a second time**. Use the citation sentences to connect them to the text. The existing literature inventory documents the versions of previously stored PDFs.

### `bojanczykFabianskiStefanski2026`

Part D references: finish the paragraph ending “from the unpublished”.

Existing PDF: [BojanczykFabianskiStefanski2026_Polyregular_Equivalence_is_Undecidable_in_Higher-Order_Types.pdf](pdfs/BojanczykFabianskiStefanski2026_Polyregular_Equivalence_is_Undecidable_in_Higher-Order_Types.pdf).

```bibtex
@article{bojanczykFabianskiStefanski2026,
  author  = {Boja{\'n}czyk, Miko{\l}aj and Fabia{\'n}ski, Grzegorz and
             Stefa{\'n}ski, Rafa{\l}},
  title   = {Polyregular equivalence is undecidable in higher-order types},
  journal = {CoRR},
  volume  = {abs/2604.11935},
  year    = {2026},
  doi     = {10.48550/arXiv.2604.11935},
  url     = {https://doi.org/10.48550/arXiv.2604.11935}
}
```

```latex
The undecidability result from \cref{thm:undecidability-higher-order} is from~\cite{bojanczykFabianskiStefanski2026}.
```

### `bojanczyk2023`

Part D references: growth rates, interpretation dimension and the distinction from pebble count.

Existing PDF: [Bojanczyk2023_On_the_growth_rates_of_polyregular_functions_preprint.pdf](pdfs/Bojanczyk2023_On_the_growth_rates_of_polyregular_functions_preprint.pdf).

```bibtex
@inproceedings{bojanczyk2023,
  author    = {Boja{\'n}czyk, Miko{\l}aj},
  title     = {On the Growth Rates of Polyregular Functions},
  booktitle = {LICS 2023},
  pages     = {1--13},
  publisher = {IEEE},
  year      = {2023},
  note      = {The author version, 24 pages against the 13 of the proceedings
               version, is available as arXiv:2212.11631 under the title
               \emph{On the growth rate of polyregular functions}},
  doi       = {10.1109/LICS56636.2023.10175808},
  url       = {https://doi.org/10.1109/LICS56636.2023.10175808}
}
```

```latex
For further results on growth rates of polyregular functions, see~\cite{bojanczyk2023}.
```

### `courcelleEngelfriet2012`

Parts C and D: general background on MSO transductions and interpretations.

Existing PDF: [CourcelleEngelfriet2012_Graph_Structure_and_Monadic_Second-Order_Logic.pdf](pdfs/CourcelleEngelfriet2012_Graph_Structure_and_Monadic_Second-Order_Logic.pdf).

```bibtex
@book{courcelleEngelfriet2012,
  author    = {Courcelle, Bruno and Engelfriet, Joost},
  title     = {Graph Structure and Monadic Second-Order Logic: A Language-Theoretic Approach},
  publisher = {Cambridge University Press},
  year      = {2012},
  doi       = {10.1017/CBO9780511977619},
  url       = {https://doi.org/10.1017/CBO9780511977619}
}
```

```latex
For a general treatment of transformations defined by monadic second-order logic, see~\cite{courcelleEngelfriet2012}.
```

### `engelfriet2015`

Part D references: composition for partial pebble transductions.

Existing PDF: [Engelfriet2015_Two-way_pebble_transducers_for_partial_functions_and_their_composition.pdf](pdfs/Engelfriet2015_Two-way_pebble_transducers_for_partial_functions_and_their_composition.pdf).

```bibtex
@article{engelfriet2015,
  author  = {Engelfriet, Joost},
  title   = {Two-way pebble transducers for partial functions and their composition},
  journal = {Acta Informatica},
  year    = {2015},
  doi     = {10.1007/s00236-015-0224-3},
  url     = {https://doi.org/10.1007/s00236-015-0224-3}
}
```

```latex
Composition for partial pebble transductions is treated in~\cite{engelfriet2015}.
```

### `bealLombardySakarovitch2006`

Part B references: weighted-automata equivalence and functional transducers.

Existing PDF: [BealLombardySakarovitch2006_Conjugacy_and_Equivalence_of_Weighted_Automata_and_Functional_Transducers.pdf](pdfs/BealLombardySakarovitch2006_Conjugacy_and_Equivalence_of_Weighted_Automata_and_Functional_Transducers.pdf).

```bibtex
@inbook{bealLombardySakarovitch2006,
  author    = {B{\'e}al, Marie-Pierre and Lombardy, Sylvain and Sakarovitch, Jacques},
  title     = {Conjugacy and equivalence of weighted automata and functional transducers},
  booktitle = {Computer Science -- Theory and Applications},
  pages     = {58--69},
  year      = {2006},
  publisher = {Springer Berlin Heidelberg},
  doi       = {10.1007/11753728_9},
  url       = {https://doi.org/10.1007/11753728_9}
}
```

```latex
For further connections between weighted automata and functional transducers, see~\cite{bealLombardySakarovitch2006}.
```

### `BerstelReutenauer1988`

Part B: systematic background for rational series and weighted automata.

Existing PDF: [BerstelReutenauer1988_Rational_Series_and_Their_Languages.pdf](pdfs/BerstelReutenauer1988_Rational_Series_and_Their_Languages.pdf).

```bibtex
@book{BerstelReutenauer1988,
  author    = {Berstel, Jean and Reutenauer, Christophe},
  title     = {Rational Series and Their Languages},
  series    = {EATCS Monographs on Theoretical Computer Science},
  volume    = {12},
  publisher = {Springer},
  address   = {Berlin},
  year      = {1988},
  isbn      = {978-0-387-18626-9},
  note      = {Cited according to the electronic edition of 6 November 2006; a
               revised and extended version appeared as \emph{Noncommutative
               Rational Series with Applications}, Cambridge University Press,
               2010}
}
```

```latex
A systematic account of rational series can be found in~\cite{BerstelReutenauer1988}.
```

### `alurCerny2011`

Part C references: SST applications to verification of list-processing programs.

Existing PDF: [AlurCerny2011_Streaming_Transducers_for_Algorithmic_Verification_of_Single-Pass_List-Processing_Programs.pdf](pdfs/AlurCerny2011_Streaming_Transducers_for_Algorithmic_Verification_of_Single-Pass_List-Processing_Programs.pdf).

```bibtex
@inproceedings{alurCerny2011,
  author    = {Alur, Rajeev and {\v{C}}ern{\'y}, Pavol},
  title     = {Streaming Transducers for Algorithmic Verification of Single-Pass List-Processing Programs},
  booktitle = {POPL 2011},
  year      = {2011},
  doi       = {10.1145/1926385.1926454},
  url       = {https://doi.org/10.1145/1926385.1926454}
}
```

```latex
An application of streaming transducers to verification of list-processing programs is presented in~\cite{alurCerny2011}.
```

### `muschollPuppis2019`

Introduction or Part C references: an overview of string transducers.

Existing PDF: [MuschollPuppis2019_The_Many_Facets_of_String_Transducers.pdf](pdfs/MuschollPuppis2019_The_Many_Facets_of_String_Transducers.pdf).

```bibtex
@inproceedings{muschollPuppis2019,
  author    = {Muscholl, Anca and Puppis, Gabriele},
  title     = {The Many Facets of String Transducers (Invited Talk)},
  booktitle = {STACS 2019},
  year      = {2019},
  doi       = {10.4230/LIPIcs.STACS.2019.2},
  url       = {https://doi.org/10.4230/LIPIcs.STACS.2019.2}
}
```

```latex
For a survey of string transducers, see~\cite{muschollPuppis2019}.
```

### `nivat1968`

Part B references: historical background on rational transductions.

Existing PDF: [Nivat1968_Transductions_des_langages_de_Chomsky.pdf](pdfs/Nivat1968_Transductions_des_langages_de_Chomsky.pdf).

```bibtex
@article{nivat1968,
  author  = {Nivat, Maurice},
  title   = {Transductions des langages de Chomsky},
  journal = {Annales de l'Institut Fourier},
  volume  = {18},
  number  = {1},
  pages   = {339--455},
  year    = {1968},
  doi     = {10.5802/aif.287},
  url     = {https://doi.org/10.5802/aif.287}
}
```

```latex
Another classical reference for rational transductions is~\cite{nivat1968}.
```

### `eilenberg1976`

Part A references: algebraic background for Krohn--Rhodes.

No matching local PDF was identified in the existing collection.

```bibtex
@book{eilenberg1976,
  author    = {Eilenberg, Samuel},
  title     = {Automata, Languages, and Machines. Volume B},
  series    = {Pure and Applied Mathematics},
  volume    = {59-B},
  publisher = {Academic Press},
  address   = {New York},
  year      = {1976},
  isbn      = {978-0-12-234002-4},
  note      = {With two chapters by Bret Tilson}
}
```

```latex
For the algebraic perspective on decomposition of finite machines, see also~\cite{eilenberg1976}.
```

## Bibliographical-note repairs

- In `partDPolyregular/bib-notes.tex`, replace the statement that the higher-order and MSO characterisations are future additions: both chapters are already included by `main.tex`. Retain `bojanczykPolyregularFunctions2018` for higher-order terms and `bojanczykKieferLhote2019` for the MSO characterisation.
- Complete the unfinished final sentence with `\cite{bojanczykFabianskiStefanski2026}`, as suggested above.
- Do not cite `lhote2020` as an unqualified justification that growth degree determines pebble count. Any historical discussion should explain its relationship to the later counterexamples and growth results.

## Citation audit

The review found 83 entries in `bib.bib`, 18 uncited keys in the active book sources, and no unresolved citation keys. Commented-out citations were excluded. The following eight uncited entries were not selected for the ten-item placement list above:

- `kleene1951`
- `culik1978decidability`
- `CulikKarhumaki1983`
- `Sakarovitch2009`
- `filiotReynierServais2013`
- `bojanczyk2014origin`
- `wang1961`
- `lhote2020`

Their presence in the bibliography database is not by itself a reason to add a citation. Select them if the surrounding discussion needs the relevant historical or technical context.

