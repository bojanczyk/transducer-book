# Literature for Parts A-D

This folder collects the main sources to cite for the first four parts of the book.

BibTeX entries for everything listed here live in the book's bibliography, [../bib.bib](../bib.bib).

## Background

- **Emil L. Post (1946), _A Variant of a Recursively Unsolvable Problem_.**  
  The paper that introduces the Post Correspondence Problem — here still called the "correspondence decision problem" — and shows it to be recursively unsolvable. It is the source of the undecidability reductions in Part B, starting with the undecidable equivalence problem for rational relations. The statement is on p. 264.  
  DOI: https://doi.org/10.1090/S0002-9904-1946-08555-9  
  PDF: [Post1946_A_Variant_of_a_Recursively_Unsolvable_Problem.pdf](pdfs/Post1946_A_Variant_of_a_Recursively_Unsolvable_Problem.pdf) (5 pp.)

- **S. C. Kleene (1951), _Representation of Events in Nerve Nets and Finite Automata_.**  
  The origin of regular expressions and of the Kleene Theorem, which underlies the rational/recognisable material in Part B and the regular languages used throughout. Written as a RAND research memorandum, and freely available in that form; the revised version appeared in _Automata Studies_ (Shannon and McCarthy, eds.), Annals of Mathematics Studies 34, Princeton University Press, 1956, pp. 3-41.  
  RAND: https://www.rand.org/pubs/research_memoranda/RM704.html (report RM-704)  
  PDF: [Kleene1951_Representation_of_Events_in_Nerve_Nets_and_Finite_Automata.pdf](pdfs/Kleene1951_Representation_of_Events_in_Nerve_Nets_and_Finite_Automata.pdf) (RAND memorandum)

- **Dana Scott (1967), _Some Definitional Suggestions for Automata Theory_.**  
  Scott proposing a uniform terminology for the abstract machines that were multiplying at the time. Two of the proposals matter here. The first is that nondeterminism can be dispensed with — Scott, who had helped popularise it in Rabin-Scott, writes that he "now feels that it is simpler to avoid" nondeterministic machines, and Section 5 shows how the sets normally obtained from them can be defined without. The second is the separation of program from machine, developed over Sections 1-3, so that a definition need not be restated "every time an inspiration for a new machine strikes".  
  Of most relevance to a book on transducers is the emphasis Scott places on functions rather than sets: "the basic nature of a program is to compute a function", with the recognised sets recovered afterwards as they are in recursive function theory. Section 4 gives examples of machines, Section 6 miscellaneous applications.  
  DOI: https://doi.org/10.1016/S0022-0000(67)80014-X  
  PDF: [Scott1967_Some_Definitional_Suggestions_for_Automata_Theory.pdf](pdfs/Scott1967_Some_Definitional_Suggestions_for_Automata_Theory.pdf) (26 pp.)

- **Jean-Éric Pin (2025), _Mathematical Foundations of Automata Theory_ (MPRI lecture notes).**  
  General algebraic-automata-theory reference: semigroups, Green's relations, recognisable and rational sets, star-free and piecewise testable languages, varieties. The profinite material is **Chapter X, _Profinite words_, pp. 175-188** — profinite metric and topology (§2.1), free profinite monoid and its universal property (§2.2-2.3), ω-terms (§2.4), recognisable languages as clopen sets (§3).  
  Link: https://www.irif.fr/~jep/PDF/MPRI/MPRI.pdf  
  PDF: [Pin2025_Mathematical_Foundations_of_Automata_Theory.pdf](pdfs/Pin2025_Mathematical_Foundations_of_Automata_Theory.pdf) (version of 24 March 2025, 344 pp.)  
  Note: a living document, so quote the version date when citing. It is also cited in the literature as [Pin22], which is the version of 18 February 2022; Chapter X sits at pp. 175-188 in both.

- **Michael Sipser (2012), _Introduction to the Theory of Computation_, 3rd edition.**  
  Standard undergraduate textbook. Used for the modern textbook proof that the Post Correspondence Problem is undecidable (Theorem 5.15), which is what the text points the reader to.  
  ISBN: 978-1-133-18779-0  
  PDF: [Sipser2012_Introduction_to_the_Theory_of_Computation.pdf](pdfs/Sipser2012_Introduction_to_the_Theory_of_Computation.pdf) (3rd edition, 482 pp.)  
  Note: in copyright, no free electronic edition.

- **Damian Niwiński and Wojciech Rytter, edited by Filip Murlak (2017), _200 Problems in Formal Languages and Automata Theory_.**  
  Problem collection used for classical exercises. The book is cited in the text as the Cambridge University Press edition, _200 Problems on Languages, Automata, and Computation_ (2023, DOI [10.1017/9781009072632](https://doi.org/10.1017/9781009072632)); the PDF stored here is the **earlier University of Warsaw 2017 edition**, problems only, without solutions.  
  PDF: [MurlakNiwinskiRytter2017_200_Problems_in_Formal_Languages_and_Automata_Theory.pdf](pdfs/MurlakNiwinskiRytter2017_200_Problems_in_Formal_Languages_and_Automata_Theory.pdf) (University of Warsaw 2017, 65 pp.)  
  Warning: problem numbering differs between the two editions. In this 2017 edition, Problem 24 is the one about reversal, Problem 30 is Root/Sqrt/Log/Fibb, and Problem 35 is about counting factors — so the pinpoint `Problems 30 and 35` used in the text follows the 2023 numbering, not this file.

## Part A — Mealy machines

- **George H. Mealy (1955), _A Method for Synthesizing Sequential Circuits_.**  
  Origin paper for Mealy machines and letter-to-letter transducers.  
  DOI: https://doi.org/10.1002/j.1538-7305.1955.tb03788.x  
  PDF: [Mealy1955_Method_for_Synthesizing_Sequential_Circuits.pdf](pdfs/Mealy1955_Method_for_Synthesizing_Sequential_Circuits.pdf)

- **Edward F. Moore (1956), _Gedanken-Experiments on Sequential Machines_.**  
  The paper that introduces Moore machines: sequential machines whose output is determined by the state alone, rather than by the state together with the input letter as in Mealy's model above. Also the source of the "gedanken-experiment" view of a machine as something probed from the outside, of the distinguishability and machine-identification problems, and of the reduction of a machine to an equivalent one with no two equivalent states. It appeared in _Automata Studies_, the same volume as the revised version of Kleene's paper listed under Background.  
  DOI: https://doi.org/10.1515/9781400882618-006  
  Publisher: https://press.princeton.edu/books/paperback/9780691079165/automata-studies-am-34-volume-34  
  PDF: [Moore1956_Gedanken-Experiments_on_Sequential_Machines.pdf](pdfs/Moore1956_Gedanken-Experiments_on_Sequential_Machines.pdf) (offprint of the chapter, 26 pp.)

- **Anil Nerode (1958), _Linear Automaton Transformations_.**  
  The source of the Nerode right congruence, and so of the Myhill-Nerode chapter. What the paper calls an "automaton transformation" is a Mealy machine in the terminology of this book, written for maps on infinite sequences; the main result settles which linear transformations over a finite commutative ring are computed by one. The right-congruence argument used to get there is the machine-independent characterisation that the Mealy chapter treats as folklore.  
  DOI: https://doi.org/10.1090/S0002-9939-1958-0135681-9  
  PDF: [Nerode1958_Linear_Automaton_Transformations.pdf](pdfs/Nerode1958_Linear_Automaton_Transformations.pdf) (4 pp., free from the AMS)

- **Kenneth Krohn and John Rhodes (1965), _Algebraic Theory of Machines. I. Prime Decomposition Theorem for Finite Semigroups and Machines_.**  
  The classical decomposition theorem behind the book’s Krohn-Rhodes chapter.  
  DOI: https://doi.org/10.1090/S0002-9947-1965-0188316-1  
  PDF: [KrohnRhodes1965_Algebraic_Theory_of_Machines_I.pdf](pdfs/KrohnRhodes1965_Algebraic_Theory_of_Machines_I.pdf)

- **M. P. Schützenberger (1965), _On Finite Monoids Having Only Trivial Subgroups_.**  
  The characterisation of star-free languages as the ones recognised by aperiodic (group-free) monoids — one half of the Schützenberger-McNaughton-Papert theorem used in the logic chapter.  
  DOI: https://doi.org/10.1016/S0019-9958(65)90108-7  
  PDF: [Schutzenberger1965_On_Finite_Monoids_Having_Only_Trivial_Subgroups.pdf](pdfs/Schutzenberger1965_On_Finite_Monoids_Having_Only_Trivial_Subgroups.pdf) (journal offprint, 5 pp.)

- **Albert R. Meyer (1969), _A Note on Star-Free Events_.**  
  Short proof that the star-free languages are exactly the group-free (aperiodic) ones, obtained by appealing to the Krohn-Rhodes decomposition theorem above. Background for the aperiodic Mealy machines of the Krohn-Rhodes chapter.  
  DOI: https://doi.org/10.1145/321510.321513  
  PDF: [Meyer1969_A_Note_on_Star-Free_Events.pdf](pdfs/Meyer1969_A_Note_on_Star-Free_Events.pdf)

- **Robert McNaughton and Seymour Papert (1971), _Counter-Free Automata_.**  
  The monograph that assembles the equivalence between star-free languages, counter-free (aperiodic) automata, and first-order definability — the other half of the Schützenberger-McNaughton-Papert theorem.  
  ISBN: 0-262-13076-9  
  PDF: [McNaughtonPapert1971_Counter-Free_Automata.pdf](pdfs/McNaughtonPapert1971_Counter-Free_Automata.pdf) (scan, 181 pp., with a usable OCR text layer)  
  Note: in copyright, no free electronic edition.

- **Samuel Eilenberg (1976), _Automata, Languages, and Machines. Volume B_.**  
  The standard algebraic treatment of machines: wreath products, the Krohn-Rhodes decomposition, and the variety theory relating pseudovarieties of finite monoids to classes of languages. Includes two chapters by Bret Tilson on the depth decomposition theorem and on complexity. Companion to Volume A, listed under Part B below.  
  Publisher: https://shop.elsevier.com/books/automata-languages-and-machines/eilenberg/978-0-12-234002-4  
  Borrowable scan: https://archive.org/details/automatalanguage0000eile  
  No PDF stored locally (in copyright, no free electronic edition).

- **Thomas Wilke (1999), _Classifying Discrete Temporal Properties_.**  
  Survey of the classification of temporal properties, and of the methods behind it, with the connections to finite automata and to the theory of finite semigroups.  
  DOI: https://doi.org/10.1007/3-540-49116-3_3  
  PDF: [Wilke1999_Classifying_Discrete_Temporal_Properties.pdf](pdfs/Wilke1999_Classifying_Discrete_Temporal_Properties.pdf)

## Part B — Rational relations and functions

- **Paul Dubreil (1941), _Contribution à la théorie des demi-groupes. I_.**  
  Origin of right congruences in semigroup theory, the algebraic background to the Myhill-Nerode chapter. Page 8 has the definition of a right congruence, and Theorem 3 says that the relation defined there is one. Mémoires de l'Académie des Sciences de l'Institut de France, tome 63, pp. 1-52.  
  Gallica (BnF) has tome 63 digitised as ark `bpt6k3278g`; the memoir is no. 3 of the volume and occupies views 355-406, which are its pages 1-52.  
  Gallica: https://gallica.bnf.fr/ark:/12148/bpt6k3278g/f355  
  PDF: [Dubreil1941_Contribution_a_la_theorie_des_demi-groupes.pdf](pdfs/Dubreil1941_Contribution_a_la_theorie_des_demi-groupes.pdf) (assembled from the Gallica page scans; the volume has no OCR layer)  
  Note: likely still in copyright (Dubreil died 1994), and Gallica marks the volume as `sous droits`.

- **A. I. Mal'cev (1953), _Nilpotent Semigroups_.**  
  The embedding of a free monoid into a (metabelian) nilpotent group. This is the ingredient that Albert and Lawrence borrow below to turn a question about strings into a question about polynomials, and so the distant ancestor of the reduction to weighted automata used in this book.  
  No DOI — Uchenye Zapiski Ivanovskogo Gosudarstvennogo Pedagogicheskogo Instituta, Fiziko-Matematicheskie Nauki 4, pp. 107-111, in Russian.  
  No PDF stored locally.

- **M.-P. Schützenberger (1955-1956), _Une théorie algébrique du codage_.**  
  The talk in which Schützenberger set out his algebraic approach to codes, the starting point for the line of work continued in his later papers on transducers and rational relations. Séminaire Dubreil, tome 9, exposé no. 15, 24 pages.  
  Numdam: https://www.numdam.org/item/SD_1955-1956__9__A10_0/  
  PDF: [Schutzenberger1956_Une_theorie_algebrique_du_codage.pdf](pdfs/Schutzenberger1956_Une_theorie_algebrique_du_codage.pdf)

- **M. P. Schützenberger (1961), _A Remark on Finite Transducers_.**  
  Classic finite-transducer reference, especially relevant to the deterministic/function side.  
  DOI: https://doi.org/10.1016/S0019-9958(61)80006-5  
  PDF: [Schutzenberger1961_A_Remark_on_Finite_Transducers.pdf](pdfs/Schutzenberger1961_A_Remark_on_Finite_Transducers.pdf)

- **M. P. Schützenberger (1961), _On the Definition of a Family of Automata_.**  
  The paper that introduces weighted automata (Definition 1). The outputs may live in an arbitrary semiring, but the results are for a field; Section B gives the minimisation construction, from which the weighted-automata chapter derives an algorithm for zeroness, and from that one for equivalence.  
  DOI: https://doi.org/10.1016/S0019-9958(61)80020-X  
  PDF: [Schutzenberger1961_On_the_Definition_of_a_Family_of_Automata.pdf](pdfs/Schutzenberger1961_On_the_Definition_of_a_Family_of_Automata.pdf)

- **C. C. Elgot and J. E. Mezei (1965), _On Relations Defined by Generalized Finite Automata_.**  
  Foundational for rational relations and generalized finite-state transductions.  
  DOI: https://doi.org/10.1147/rd.91.0047  
  PDF: [ElgotMezei1965_On_Relations_Defined_by_Generalized_Finite_Automata.pdf](pdfs/ElgotMezei1965_On_Relations_Defined_by_Generalized_Finite_Automata.pdf)

- **Seymour Ginsburg and Gene F. Rose (1966), _A Characterization of Machine Mappings_.**  
  Useful background for deterministic string transductions and machine mappings.  
  DOI: https://doi.org/10.4153/CJM-1966-040-3  
  PDF: [GinsburgRose1966_A_Characterization_of_Machine_Mappings.pdf](pdfs/GinsburgRose1966_A_Characterization_of_Machine_Mappings.pdf)

- **Maurice Nivat (1968), _Transductions des langages de Chomsky_.**  
  One of the core papers on rational transductions.  
  DOI: https://doi.org/10.5802/aif.287  
  PDF: [Nivat1968_Transductions_des_langages_de_Chomsky.pdf](pdfs/Nivat1968_Transductions_des_langages_de_Chomsky.pdf)

- **Timothy V. Griffiths (1968), _The Unsolvability of the Equivalence Problem for Λ-Free Nondeterministic Generalized Machines_.**  
  Undecidability of equivalence for nondeterministic generalized sequential machines, by reduction from the Post Correspondence Problem; the reduction is on p. 410. This is the reference for the undecidable equivalence problem of rational relations.  
  DOI: https://doi.org/10.1145/321466.321473  
  PDF: [Griffiths1968_The_Unsolvability_of_the_Equivalence_Problem_for_Lambda-Free_Nondeterministic_Generalized_Machines.pdf](pdfs/Griffiths1968_The_Unsolvability_of_the_Equivalence_Problem_for_Lambda-Free_Nondeterministic_Generalized_Machines.pdf) (5 pp.)

- **Samuel Eilenberg and M. P. Schützenberger (1969), _Rational Sets in Commutative Monoids_.**  
  Rational subsets of a commutative monoid are exactly the semilinear ones, so over a free commutative monoid they are exactly the semilinear subsets of ℕ^k. This is the algebraic form of Parikh's theorem, and the reason rational sets stay well behaved once the order of letters is forgotten. Companion to Eilenberg's Volume A below, where the rational/recognisable machinery is developed in full.  
  DOI: https://doi.org/10.1016/0021-8693(69)90070-2  
  PDF: [EilenbergSchutzenberger1969_Rational_Sets_in_Commutative_Monoids.pdf](pdfs/EilenbergSchutzenberger1969_Rational_Sets_in_Commutative_Monoids.pdf) (19 pp.)

- **Samuel Eilenberg (1974), _Automata, Languages, and Machines. Volume A_.**  
  The classical reference for rational and recognisable sets, rational relations, and sequential machines. Also background for Part A; see Volume B under Part A above. Chapter pointers, from the table of contents:
  - Chapter VII, _Rational Sets_ (p. 159)
  - Chapter IX, _Rational Relations_ — includes the composition and factorization theorems, and rational partial functions (p. 258)
  - Chapter X, _Machines_ — §3 transducers and rational relations (p. 272), §6 two-way automata (p. 282)
  - Chapter XI, _Sequential Machines_ — §7 sequential bimachines (p. 320), §8 examples of bimachines (p. 322)
  - Chapter XII, _Operations on Sequential Machines_ — minimization (p. 338) and composition (p. 349)
  
  Publisher: https://shop.elsevier.com/books/automata-languages-and-machines/eilenberg/978-0-12-234001-7  
  PDF: [Eilenberg1974_Automata_Languages_and_Machines_Volume_A.pdf](pdfs/Eilenberg1974_Automata_Languages_and_Machines_Volume_A.pdf) (469 pp., converted from a djvu scan; the OCR text layer was carried over, so it is searchable)  
  Note: in copyright, no free electronic edition.

- **M. P. Schützenberger (1976), _Sur les relations rationnelles entre monoïdes libres_.**  
  Directly on rational relations over free monoids.  
  DOI: https://doi.org/10.1016/0304-3975(76)90026-8  
  PDF: [Schutzenberger1976_Sur_les_relations_rationnelles_entre_monoides_libres.pdf](pdfs/Schutzenberger1976_Sur_les_relations_rationnelles_entre_monoides_libres.pdf) (searchable, but the OCR is rough)  
  Also: [Schutzenberger1976_..._clean_scan.pdf](pdfs/Schutzenberger1976_Sur_les_relations_rationnelles_entre_monoides_libres_clean_scan.pdf) — a much cleaner scan of the same 17 pages, but with no text layer. Keep whichever you prefer; they are the same paper.

- **Christian Choffrut (1977), _Une caractérisation des fonctions séquentielles et des fonctions sous-séquentielles en tant que relations rationnelles_.**  
  Key paper on sequential/subsequential functions as rational relations.  
  DOI: https://doi.org/10.1016/0304-3975(77)90049-4  
  PDF: [Choffrut1977_Une_caracterisation_des_fonctions_sequentielles.pdf](pdfs/Choffrut1977_Une_caracterisation_des_fonctions_sequentielles.pdf)

- **Meera Blattner and Tom Head (1977), _Single-Valued a-Transducers_.**  
  Decidability of functionality for rational relations (Theorem 1), proved by a pumping argument, together with decidability of equivalence for the single-valued ones. The book reduces equivalence of rational functions to this, by taking unions.  
  DOI: https://doi.org/10.1016/S0022-0000(77)80033-0  
  PDF: [BlattnerHead1977_Single-Valued_a-Transducers.pdf](pdfs/BlattnerHead1977_Single-Valued_a-Transducers.pdf)

- **Karel Culik II and Arto Salomaa (1978), _On the Decidability of Homomorphism Equivalence for Languages_.**  
  Decidability of whether two homomorphisms agree on a given language — a decision problem in the immediate neighbourhood of equivalence for rational functions.  
  DOI: https://doi.org/10.1016/0022-0000(78)90002-8  
  PDF: [CulikSalomaa1978_On_the_Decidability_of_Homomorphism_Equivalence_for_Languages.pdf](pdfs/CulikSalomaa1978_On_the_Decidability_of_Homomorphism_Equivalence_for_Languages.pdf)

- **Jean Berstel (1979), _Transductions and Context-Free Languages_.**  
  The standard monograph on rational transductions; the free 2009 electronic edition covers the first four chapters, including the general theory of rational transductions.  
  Link: https://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions14dec2009.pdf  
  PDF: [Berstel1979_Transductions_and_Context-Free_Languages.pdf](pdfs/Berstel1979_Transductions_and_Context-Free_Languages.pdf) (electronic edition, 14 Dec 2009)

- **Karel Culik II and Juhani Karhumäki (1983), _Systems of Equations over a Free Monoid and Ehrenfeucht's Conjecture_.**  
  Recasts Ehrenfeucht's conjecture as a compactness statement: it holds if and only if every infinite system of equations over a free monoid is equivalent to a finite subsystem. The reformulation that set up the proof in the next item.  
  DOI: https://doi.org/10.1016/0012-365X(83)90152-8  
  PDF: [CulikKarhumaki1983_Systems_of_Equations_over_a_Free_Monoid_and_Ehrenfeuchts_Conjecture.pdf](pdfs/CulikKarhumaki1983_Systems_of_Equations_over_a_Free_Monoid_and_Ehrenfeuchts_Conjecture.pdf)

- **Michael H. Albert and John Lawrence (1985), _A Proof of Ehrenfeucht's Conjecture_.**  
  Proves the conjecture in three pages, by embedding strings into the metabelian group (after Mal'cev above) and applying Hilbert's Basis Theorem. Theorem 1 is where the equivalence-by-algebra reduction of Part B ultimately comes from, and the same approach settles HD0L equivalence — which is the copyful SST equivalence of Part C.  
  DOI: https://doi.org/10.1016/0304-3975(85)90066-0  
  PDF: [AlbertLawrence1985_A_Proof_of_Ehrenfeuchts_Conjecture.pdf](pdfs/AlbertLawrence1985_A_Proof_of_Ehrenfeuchts_Conjecture.pdf)

- **Jean Berstel and Christophe Reutenauer (1988), _Rational Series and Their Languages_.**  
  The standard monograph on rational series over a semiring: recognisable series, Schützenberger's minimisation and equivalence theory, and the language-theoretic consequences. Companion reference for the weighted-automata chapter.  
  Book page: http://www-igm.univ-mlv.fr/~berstel/LivreSeries/LivreSeries.html  
  PDF: [BerstelReutenauer1988_Rational_Series_and_Their_Languages.pdf](pdfs/BerstelReutenauer1988_Rational_Series_and_Their_Languages.pdf) (electronic edition of 6 November 2006, 148 pp.)  
  Note: the printed editions (Masson 1984 in French, Springer EATCS Monographs 1988 in English) are out of print; a revised and extended version appeared as _Noncommutative Rational Series with Applications_, Cambridge University Press, 2010.

- **Tero Harju and Juhani Karhumäki (1991), _The Equivalence Problem of Multitape Finite Automata_.**  
  Decidability of equivalence for multitape automata, obtained by reduction to equivalence of weighted automata. The weighted-automata chapter traces its own reduction back to this paper; the two differences are the source (equivalence of (tuple-of-string)-to-Boolean functions, rather than of rational string-to-string functions) and the target (weighted automata over a division ring, rather than over a field), which is why Harju and Karhumäki have to extend Schützenberger's argument from a field to a division ring.  
  DOI: https://doi.org/10.1016/0304-3975(91)90356-7  
  PDF: [HarjuKarhumaki1991_The_Equivalence_Problem_of_Multitape_Finite_Automata.pdf](pdfs/HarjuKarhumaki1991_The_Equivalence_Problem_of_Multitape_Finite_Automata.pdf)

- **Christophe Reutenauer and Marcel-Paul Schützenberger (1991), _Minimization of Rational Word Functions_.**  
  Minimisation for rational word functions. Theorem 4.1 is the machine-independent characterisation of the rational functions used in the Myhill-Nerode chapter; the introduction is also where Schützenberger appears to credit the name "rational" for string functions to Eilenberg.  
  DOI: https://doi.org/10.1137/0220042  
  PDF: [ReutenauerSchutzenberger1991_Minimization_of_Rational_Word_Functions.pdf](pdfs/ReutenauerSchutzenberger1991_Minimization_of_Rational_Word_Functions.pdf) (17 pp.)

- **Marie-Pierre Béal, Sylvain Lombardy, and Jacques Sakarovitch (2006), _Conjugacy and Equivalence of Weighted Automata and Functional Transducers_.**  
  Useful for the weighted-automata route to equivalence of rational functions.  
  DOI: https://doi.org/10.1007/11753728_9  
  PDF: [BealLombardySakarovitch2006_Conjugacy_and_Equivalence_of_Weighted_Automata_and_Functional_Transducers.pdf](pdfs/BealLombardySakarovitch2006_Conjugacy_and_Equivalence_of_Weighted_Automata_and_Functional_Transducers.pdf)

- **Jacques Sakarovitch (2009), _Elements of Automata Theory_.**  
  Comprehensive modern treatment of automata, rational relations, transducers and weighted automata, in the tradition of Eilenberg and Berstel. General-purpose reference for most of Part B.  
  DOI: https://doi.org/10.1017/CBO9781139195218  
  PDF: [Sakarovitch2009_Elements_of_Automata_Theory.pdf](pdfs/Sakarovitch2009_Elements_of_Automata_Theory.pdf) (English translation by Reuben Thomas, 784 pp.)  
  Note: in copyright, no free electronic edition.

- **Marcel-Paul Schützenberger (2009), _Œuvres complètes, Tome 8_, edited by Jean Berstel, Alain Lascoux and Dominique Perrin.**  
  The collected papers of 1971-1975, together with the editors' comments. It is those comments that the book cites for the observation that functionality of rational relations is already solved implicitly in Schützenberger's 1976 paper above.  
  Link: https://www-igm.univ-mlv.fr/~berstel/Mps/Oeuvres-Completes/tome08.pdf  
  PDF: [Schutzenberger2009_Oeuvres_completes_Tome_8.pdf](pdfs/Schutzenberger2009_Oeuvres_completes_Tome_8.pdf) (266 pp., in French)

- **Michael Benedikt, Timothy Duff, Aditya Sharad, and James Worrell (2017), _Polynomial Automata: Zeroness and Applications_.**  
  The paper that introduces polynomial automata, as a generalisation of weighted automata over a field, and settles the complexity of the Zeroness Problem for them: non-primitive recursive in general, primitive recursive for a subclass. Relevant to the weighted-automata chapter.  
  DOI: https://doi.org/10.1109/LICS.2017.8005101  
  PDF: [Benedikt2017_Polynomial_Automata_Zeroness_and_Applications.pdf](pdfs/Benedikt2017_Polynomial_Automata_Zeroness_and_Applications.pdf) (author copy, Oxford Research Archive)

- **Helmut Seidl, Sebastian Maneth, and Gregor Kemper (2018), _Equivalence of Deterministic Top-Down Tree-to-String Transducers Is Decidable_.**  
  Settles a long-standing open problem, by way of polynomial transducers and inductive invariants of polynomial ideals — the same multilinear-algebra toolkit as the polynomial automata above, applied to tree-to-string transducers.  
  DOI: https://doi.org/10.1145/3182653  
  PDF: [SeidlManethKemper2018_Equivalence_of_Deterministic_Top-Down_Tree-to-String_Transducers_Is_Decidable.pdf](pdfs/SeidlManethKemper2018_Equivalence_of_Deterministic_Top-Down_Tree-to-String_Transducers_Is_Decidable.pdf)

- **Mikołaj Bojańczyk (2019), _The Hilbert Method for Transducer Equivalence_.**  
  Expository account of the Hilbert method — encoding words and trees as numbers and polynomials, then reasoning with Hilbert's Basis Theorem — as applied to equivalence for register transducers. The simple rational-number encoding used in this book is discussed on p. 6.  
  DOI: https://doi.org/10.1145/3313909.3313911  
  PDF: [Bojanczyk2019_The_Hilbert_Method_for_Transducer_Equivalence.pdf](pdfs/Bojanczyk2019_The_Hilbert_Method_for_Transducer_Equivalence.pdf)

- **Jacques Sakarovitch (2021), _Automata and Rational Expressions_.**  
  Handbook chapter on rational and recognisable subsets of a monoid, rational expressions and the Kleene theorem. This is the detailed discussion, with ample references, that the text points to for the rational/recognisable terminology.  
  DOI: https://doi.org/10.4171/AUTOMATA-1/2  
  PDF: [Sakarovitch2021_Automata_and_Rational_Expressions.pdf](pdfs/Sakarovitch2021_Automata_and_Rational_Expressions.pdf) (arXiv:1502.03573v1, 12 February 2015, 49 pp.)  
  Warning: the stored PDF is the **extended arXiv version**, which carries proofs, examples and remarks that were cut from the published chapter for space. Its author notes that the numbering of theorems and definitions may differ between the two, so a pinpoint citation needs to say which version it means.

## Part C — Regular functions

- **Michael O. Rabin and Dana Scott (1959), _Finite Automata and Their Decision Problems_.**  
  Classic source for two-way vs one-way automata background used in regular transducer proofs.  
  DOI: https://doi.org/10.1147/rd.32.0114  
  PDF: [RabinScott1959_Finite_automata_and_their_decision_problems.pdf](pdfs/RabinScott1959_Finite_automata_and_their_decision_problems.pdf)

- **J. C. Shepherdson (1959), _The Reduction of Two-Way Automata to One-Way Automata_.**  
  Independent two-way-to-one-way reduction; historically relevant for the two-way transducer viewpoint.  
  DOI: https://doi.org/10.1147/rd.32.0198  
  PDF: [Shepherdson1959_The_reduction_of_two-way_automata_to_one-way_automata.pdf](pdfs/Shepherdson1959_The_reduction_of_two-way_automata_to_one-way_automata.pdf)

- **J. Richard Büchi (1960), _Weak Second-Order Arithmetic and Finite Automata_.**  
  One of the three independent original proofs of what is now the Büchi-Elgot-Trakhtenbrot theorem: a language of finite words is definable in monadic second-order logic exactly when it is regular. Büchi's route is through weak second-order arithmetic, and the paper also settles the decidability of that theory by the automaton translation.  
  DOI: https://doi.org/10.1002/malq.19600060105  
  PDF: [Buchi1960_Weak_Second-Order_Arithmetic_and_Finite_Automata.pdf](pdfs/Buchi1960_Weak_Second-Order_Arithmetic_and_Finite_Automata.pdf) (27 pp.)

- **Calvin C. Elgot (1961), _Decision Problems of Finite Automata Design and Related Arithmetics_.**  
  The second of the three independent proofs, developed as a theory of finite automata design: it sets up the back-and-forth translation between automata and formulas explicitly, and derives the decision procedures from it.  
  DOI: https://doi.org/10.1090/S0002-9947-1961-0139530-9  
  PDF: [Elgot1961_Decision_Problems_of_Finite_Automata_Design_and_Related_Arithmetics.pdf](pdfs/Elgot1961_Decision_Problems_of_Finite_Automata_Design_and_Related_Arithmetics.pdf) (31 pp., free from the AMS)

- **B. A. Trakhtenbrot (1962), _Finite Automata and the Logic of One-Place Predicates_.**  
  The third independent proof, published in Russian as «Конечные автоматы и логика одноместных предикатов» in Сибирский математический журнал 3:1 (1962), pp. 103-131. The English translation appeared in _American Mathematical Society Translations, Series 2_, volume 59, _Twelve Papers on Logic and Algebra_, 1966, pp. 23-55.  
  Math-Net.Ru: https://www.mathnet.ru/eng/smj4799  
  DOI of the translation: https://doi.org/10.1090/trans2/059/02  
  PDF: [Trakhtenbrot1962_Konechnye_avtomaty_i_logika_odnomestnyh_predikatov.pdf](pdfs/Trakhtenbrot1962_Konechnye_avtomaty_i_logika_odnomestnyh_predikatov.pdf) (the Russian original, 29 pp., scanned by Math-Net.Ru; no text layer)

- **J. E. Hopcroft and J. D. Ullman (1967), _An Approach to a Unified Theory of Automata_.**  
  Early decomposition-style techniques related to crossing-sequence arguments in this part.  
  DOI: https://doi.org/10.1109/FOCS.1967.4  
  PDF: [HopcroftUllman1967_An_Approach_to_a_Unified_Theory_of_Automata.pdf](pdfs/HopcroftUllman1967_An_Approach_to_a_Unified_Theory_of_Automata.pdf)

- **A. V. Aho, J. E. Hopcroft, and J. D. Ullman (1969), _A General Theory of Translation_.**  
  Introduces balloon automata, a general machine model parameterised by an auxiliary storage device. The two-way transducer of this book is exactly a balloon automaton with no auxiliary storage, so this is one of the papers where the transducer model becomes recognisable.  
  DOI: https://doi.org/10.1007/BF01703920  
  PDF: [AhoHopcroftUllman1969_A_General_Theory_of_Translation.pdf](pdfs/AhoHopcroftUllman1969_A_General_Theory_of_Translation.pdf) (29 pp.)

- **A. V. Aho and J. D. Ullman (1970), _A Characterization of Two-Way Deterministic Classes of Languages_.**  
  Theorem 2 is the first proof that two-way transducers are closed under pre-composition with Mealy machines, by an ingenious direct construction. The book proves the same result by appealing to decompositions into prime functions, which avoids the construction.  
  DOI: https://doi.org/10.1016/S0022-0000(70)80027-7  
  PDF: [AhoUllman1970_A_Characterization_of_Two-Way_Deterministic_Classes_of_Languages.pdf](pdfs/AhoUllman1970_A_Characterization_of_Two-Way_Deterministic_Classes_of_Languages.pdf)

- **Michal P. Chytil and Vojtěch Jákl (1977), _Serial Composition of 2-Way Finite-State Transducers and Simple Programs on Strings_.**  
  The first proof that two-way transducers are closed under composition — the theorem that makes the class of regular functions robust, and one of the central results of this part.  
  DOI: https://doi.org/10.1007/3-540-08342-1_11  
  PDF: [ChytilJakl1977_Serial_Composition_of_2-Way_Finite-State_Transducers_and_Simple_Programs_on_Strings.pdf](pdfs/ChytilJakl1977_Serial_Composition_of_2-Way_Finite-State_Transducers_and_Simple_Programs_on_Strings.pdf)

- **Eitan M. Gurari (1982), _The Equivalence Problem for Deterministic Two-Way Sequential Transducers Is Decidable_.**  
  Decidability of equivalence for deterministic two-way transducers — the counterpart, on the two-way side, of the equivalence results for rational functions in Part B. A preliminary version appeared at FOCS 1980, pp. 83-85.  
  DOI: https://doi.org/10.1137/0211035  
  PDF: [Gurari1982_The_Equivalence_Problem_for_Deterministic_Two-Way_Sequential_Transducers_is_Decidable.pdf](pdfs/Gurari1982_The_Equivalence_Problem_for_Deterministic_Two-Way_Sequential_Transducers_is_Decidable.pdf) (5 pp.)

- **Wolfgang Thomas (1997), _Languages, Automata, and Logic_.**  
  The standard survey of the automata-logic connection: the Büchi-Elgot-Trakhtenbrot theorem above and its many descendants, over finite and infinite words and over trees, together with the star-free/first-order correspondence. The obvious place to send a reader who wants the whole landscape of the logic chapter in one piece.  
  DOI: https://doi.org/10.1007/978-3-642-59126-6_7  
  PDF: [Thomas1997_Languages_Automata_and_Logic.pdf](pdfs/Thomas1997_Languages_Automata_and_Logic.pdf) (the chapter, pp. 389-455, 67 pp. scanned)

- **Mikołaj Bojańczyk (2025), _An Automata Toolbox_.**  
  Modern lecture-note reference used repeatedly for regular-transducer arguments and proofs.  
  Link: https://www.mimuw.edu.pl/~bojan/paper/automata-toolbox-book  
  PDF: [Bojanczyk2025_An_Automata_Toolbox.pdf](pdfs/Bojanczyk2025_An_Automata_Toolbox.pdf) (version of 30 December 2025, 293 pp.)  
  Note: a living document; dated versions are kept alongside it at mimuw.edu.pl/~bojan/papers/.

### SST and MSO transductions (Part C focus)

- **Rajeev Alur and Pavol Černý (2010), _Expressiveness of Streaming String Transducers_.**  
  Core SST paper: defines the model and connects it to regular string-to-string transductions.  
  DOI: https://doi.org/10.4230/LIPIcs.FSTTCS.2010.1  
  PDF: [AlurCerny2010_Expressiveness_of_Streaming_String_Transducers.pdf](pdfs/AlurCerny2010_Expressiveness_of_Streaming_String_Transducers.pdf) (FSTTCS 2010, LIPIcs vol. 8, open access under CC-BY)

- **Rajeev Alur and Pavol Černý (2011), _Streaming Transducers for Algorithmic Verification of Single-Pass List-Processing Programs_.**  
  Foundational verification-oriented SST perspective, with strong algorithmic motivations.  
  DOI: https://doi.org/10.1145/1926385.1926454  
  PDF: [AlurCerny2011_Streaming_Transducers_for_Algorithmic_Verification_of_Single-Pass_List-Processing_Programs.pdf](pdfs/AlurCerny2011_Streaming_Transducers_for_Algorithmic_Verification_of_Single-Pass_List-Processing_Programs.pdf)

- **Joost Engelfriet and Sebastian Maneth (1999), _Macro Tree Transducers, Attribute Grammars, and MSO Definable Tree Translations_.**  
  The tree counterpart of the string result below: MSO definable tree translations are exactly those computed by macro tree transducers of linear size increase, equivalently by attribute grammars in a suitable normal form. One of the papers that made "MSO transduction = machine model" a general pattern rather than a one-off.  
  DOI: https://doi.org/10.1006/inco.1999.2807  
  PDF: [EngelfrietManeth1999_Macro_Tree_Transducers_Attribute_Grammars_and_MSO_Definable_Tree_Translations.pdf](pdfs/EngelfrietManeth1999_Macro_Tree_Transducers_Attribute_Grammars_and_MSO_Definable_Tree_Translations.pdf) (58 pp.)

- **Roderick Bloem and Joost Engelfriet (2000), _A Comparison of Tree Transductions Defined by Monadic Second Order Logic and by Attribute Grammars_.**  
  Sorts out exactly how the MSO-definable tree transductions sit inside the ones given by attribute grammars, and which restrictions on attribute grammars bring the two together. The systematic comparison behind the equivalence in the previous item.  
  DOI: https://doi.org/10.1006/jcss.1999.1684  
  PDF: [BloemEngelfriet2000_A_Comparison_of_Tree_Transductions_Defined_by_Monadic_Second_Order_Logic_and_by_Attribute_Grammars.pdf](pdfs/BloemEngelfriet2000_A_Comparison_of_Tree_Transductions_Defined_by_Monadic_Second_Order_Logic_and_by_Attribute_Grammars.pdf) (50 pp.)

- **Joost Engelfriet and Hendrik Jan Hoogeboom (2001), _MSO Definable String Transductions and Two-Way Finite-State Transducers_.**  
  Landmark equivalence result between logic-based and automata-based regular transduction models.  
  Link: https://doi.org/10.1145/371316.371512  
  PDF: [EngelfrietHoogeboom2001_MSO_Definable_String_Transductions_and_Two-Way_Finite-State_Transducers.pdf](pdfs/EngelfrietHoogeboom2001_MSO_Definable_String_Transductions_and_Two-Way_Finite-State_Transducers.pdf)

- **Bruno Courcelle and Joost Engelfriet (2012), _Graph Structure and Monadic Second-Order Logic_.**  
  Standard reference for the MSO transduction framework used across strings, trees, and graphs.  
  Link: https://doi.org/10.1017/CBO9780511977619  
  PDF: [CourcelleEngelfriet2012_Graph_Structure_and_Monadic_Second-Order_Logic.pdf](pdfs/CourcelleEngelfriet2012_Graph_Structure_and_Monadic_Second-Order_Logic.pdf)

- **Emmanuel Filiot, Pierre-Alain Reynier, and Arnaud Servais (2013), _From Two-Way to One-Way Finite State Transducers_.**  
  Key one-way-definability result for regular transductions, tightly related to SST/MSO equivalence landscape.  
  Link: https://doi.org/10.1109/LICS.2013.45  
  PDF: [FiliotReynierServais2013_From_Two-Way_to_One-Way_Finite_State_Transducers.pdf](pdfs/FiliotReynierServais2013_From_Two-Way_to_One-Way_Finite_State_Transducers.pdf)

- **Rajeev Alur, Adam Freilich, and Mukund Raghothaman (2014), _Regular Combinators for String Transformations_.**  
  The reference for the combinators chapter: a machine-independent syntax for the regular functions in the spirit of regular expressions, built from constant functions by combinators rather than from states. The setting is functions from strings into a monoid. Over a commutative monoid, choice, split sum and iterated sum suffice — the analogues of union, concatenation and Kleene star, but with unambiguous parsing enforced. The main result covers the non-commutative case, which is the string-to-string one: it needs the left-additive versions of split and iterated sum (giving reversal), sum of functions (giving copying), and either function composition or a chained sum.  
  DOI: https://doi.org/10.1145/2603088.2603151  
  PDF: [AlurFreilichRaghothaman2014_Regular_Combinators_for_String_Transformations.pdf](pdfs/AlurFreilichRaghothaman2014_Regular_Combinators_for_String_Transformations.pdf) (full version, arXiv:1402.3021, 15 pp., with the proofs and constructions cut from the 10-page proceedings version)

- **Mikołaj Bojańczyk (2014), _Transducers with Origin Information_.**  
  Origin semantics viewpoint that clarifies and unifies regular string transducer models.  
  Link: https://doi.org/10.1007/978-3-662-43951-7_10  
  PDF: [Bojanczyk2014_Transducers_with_Origin_Information.pdf](pdfs/Bojanczyk2014_Transducers_with_Origin_Information.pdf)

- **Félix Baschenis, Olivier Gauwin, Anca Muscholl, and Gabriele Puppis (2017), _Untwisting Two-Way Transducers in Elementary Time_.**  
  Elementary-complexity algorithm for deciding one-way definability of a two-way transducer, and for sweeping transducers; sharpens the Filiot-Reynier-Servais result above.  
  DOI: https://doi.org/10.1109/LICS.2017.8005138  
  PDF: [Baschenis2017_Untwisting_Two-Way_Transducers_in_Elementary_Time.pdf](pdfs/Baschenis2017_Untwisting_Two-Way_Transducers_in_Elementary_Time.pdf)

- **Mikołaj Bojańczyk, Laure Daviaud, and Shankara Narayanan Krishna (2018), _Regular and First-Order List Functions_.**  
  The list-function view of regular transductions: a combinator language over lists, with a first-order fragment, shown equivalent to the regular string-to-string functions. Direct background for the regular list functions chapter.  
  DOI: https://doi.org/10.1145/3209108.3209163  
  PDF: [BojanczykDaviaudKrishna2018_Regular_and_First-Order_List_Functions.pdf](pdfs/BojanczykDaviaudKrishna2018_Regular_and_First-Order_List_Functions.pdf) (LICS 2018 proceedings version, 10 pp. — this is the one the entry cites)  
  Also: [BojanczykDaviaudKrishna2018_..._extended_arxiv.pdf](pdfs/BojanczykDaviaudKrishna2018_Regular_and_First-Order_List_Functions_extended_arxiv.pdf) — the extended preprint (arXiv:1803.06168, 32 pp.), which carries the proofs cut from the proceedings version. Theorem and definition numbers differ between the two, so a pinpoint citation needs to say which one it means.

- **Anca Muscholl and Gabriele Puppis (2019), _The Many Facets of String Transducers (Invited Talk)_.**  
  Compact survey of equivalent regular transducer models (two-way, SST, MSO, and related viewpoints).  
  DOI: https://doi.org/10.4230/LIPIcs.STACS.2019.2  
  PDF: [MuschollPuppis2019_The_Many_Facets_of_String_Transducers.pdf](pdfs/MuschollPuppis2019_The_Many_Facets_of_String_Transducers.pdf)

- **Mikołaj Bojańczyk and Rafał Stefański (2020), _Single-Use Automata and Transducers for Infinite Alphabets_.**  
  Carries the register-automata and register-transducer models over to infinite alphabets under a single-use restriction, which is what makes the resulting classes behave like the regular functions of this part rather than degenerating.  
  DOI: https://doi.org/10.4230/LIPIcs.ICALP.2020.113  
  PDF: [BojanczykStefanski2020_Single-Use_Automata_and_Transducers_for_Infinite_Alphabets.pdf](pdfs/BojanczykStefanski2020_Single-Use_Automata_and_Transducers_for_Infinite_Alphabets.pdf) (ICALP 2020, LIPIcs vol. 168, open access under CC-BY)

- **Lê Thành Dũng (Tito) Nguyễn (2024), _Two or three things I know about tree transducers_.**  
  A short cheat sheet for the tree side of this part: what a macro tree transducer actually does, and how top-down tree(-to-string), multi bottom-up, tree-walking and (invisible) pebble tree transducers, MSO transductions and unfoldings of term graphs relate to one another, especially under composition. Collects results scattered across the older literature — much of it Engelfriet's, including the two 1999/2000 papers above — into one place, which makes it the quickest route into that literature.  
  DOI: https://doi.org/10.48550/arXiv.2409.03169  
  PDF: [Nguyen2024_Two_or_three_things_I_know_about_tree_transducers.pdf](pdfs/Nguyen2024_Two_or_three_things_I_know_about_tree_transducers.pdf) (arXiv:2409.03169, 13 pp., unpublished note)

## Part D — Polyregular functions

- **Mikołaj Bojańczyk (2018), _Polyregular Functions_.**  
  Main reference introducing polyregular functions and key equivalent models.  
  Link: https://arxiv.org/abs/1810.08760  
  DOI: https://doi.org/10.48550/arXiv.1810.08760  
  PDF: [Bojanczyk2018_Polyregular_Functions.pdf](pdfs/Bojanczyk2018_Polyregular_Functions.pdf) (arXiv v1, 20 Oct 2018, 95 pp.)

- **Mikołaj Bojańczyk (2022), _Transducers of Polynomial Growth_.**  
  LICS paper developing the polynomial-growth perspective for string transductions.  
  DOI: https://doi.org/10.1145/3531130.3533326  
  DBLP: https://dblp.org/rec/conf/lics/Bojanczyk22  
  PDF: [Bojanczyk2022_Transducers_of_polynomial_growth_preprint.pdf](pdfs/Bojanczyk2022_Transducers_of_polynomial_growth_preprint.pdf) (author preprint)

- **Mikołaj Bojańczyk (2023), _On the Growth Rates of Polyregular Functions_.**  
  The follow-up to the previous item, and the reference for the growth-rate classification: a polyregular function has output size O(n^k) exactly when it is definable by an mso interpretation of dimension k. It also separates the two models, by exhibiting for every k a polyregular function of quadratic output size that needs at least k pebbles — so the dimension hierarchy and the pebble hierarchy do not line up.  
  DOI: https://doi.org/10.1109/LICS56636.2023.10175808  
  PDF: [Bojanczyk2023_On_the_growth_rates_of_polyregular_functions_preprint.pdf](pdfs/Bojanczyk2023_On_the_growth_rates_of_polyregular_functions_preprint.pdf) (author version, arXiv:2212.11631v3, 24 pp. — titled "On the growth rate of polyregular functions", singular, unlike the proceedings version)

- **Oscar H. Ibarra (1971), _Characterizations of Some Tape and Time Complexity Classes of Turing Machines in Terms of Multihead and Auxiliary Stack Automata_.**  
  Multihead automata correspond to logarithmic space; the reference for what pebble transducers would become without the stack discipline.  
  DOI: https://doi.org/10.1016/S0022-0000(71)80029-6  
  PDF: [Ibarra1971_Characterizations_of_Some_Tape_and_Time_Complexity_Classes.pdf](pdfs/Ibarra1971_Characterizations_of_Some_Tape_and_Time_Complexity_Classes.pdf)

- **Noa Globerman and David Harel (1996), _Complexity Results for Two-Way and Multi-Pebble Automata and their Logics_.**  
  Foundational complexity background for pebble-style models and stack-discipline discussions.  
  DOI: https://doi.org/10.1016/S0304-3975(96)00119-3  
  PDF: [GlobermanHarel1996_Complexity_Results_for_Two-Way_and_Multi-Pebble_Automata.pdf](pdfs/GlobermanHarel1996_Complexity_Results_for_Two-Way_and_Multi-Pebble_Automata.pdf)

- **Tova Milo, Dan Suciu, and Victor Vianu (2003), _Typechecking for XML Transformers_.**  
  Introduces pebble-transducer machinery in the XML-transformation setting.  
  DOI: https://doi.org/10.1016/S0022-0000(02)00030-2  
  PDF: [MiloSuciuVianu2003_Typechecking_for_XML_Transformers.pdf](pdfs/MiloSuciuVianu2003_Typechecking_for_XML_Transformers.pdf)

- **Joost Engelfriet and Sebastian Maneth (2002), _Two-Way Finite State Transducers with Nested Pebbles_.**  
  Important bridge between nested-pebble transducers and string/tree transduction formalisms.  
  DOI: https://doi.org/10.1007/3-540-45687-2_19  
  PDF: [EngelfrietManeth2002_Two-Way_Finite_State_Transducers_with_Nested_Pebbles.pdf](pdfs/EngelfrietManeth2002_Two-Way_Finite_State_Transducers_with_Nested_Pebbles.pdf)

- **Joost Engelfriet, Hendrik Jan Hoogeboom, and Bart Samwel (2007), _XML Transformation by Tree-Walking Transducers with Invisible Pebbles_.**  
  The unbounded-pebble variant, where invisible pebbles lift the constant bound on stack height.  
  DOI: https://doi.org/10.1145/1265530.1265540  
  PDF: [EngelfrietHoogeboomSamwel2007_XML_Transformation_by_Tree-Walking_Transducers_with_Invisible_Pebbles.pdf](pdfs/EngelfrietHoogeboomSamwel2007_XML_Transformation_by_Tree-Walking_Transducers_with_Invisible_Pebbles.pdf)

- **Joost Engelfriet (2015), _Two-way pebble transducers for partial functions and their composition_.**  
  Refines the pebble-transducer landscape used in polyregular characterizations.  
  DOI: https://doi.org/10.1007/s00236-015-0224-3  
  PDF: [Engelfriet2015_Two-way_pebble_transducers_for_partial_functions_and_their_composition.pdf](pdfs/Engelfriet2015_Two-way_pebble_transducers_for_partial_functions_and_their_composition.pdf)

- **Mikołaj Bojańczyk, Sandra Kiefer, and Nathan Lhote (2019), _String-to-String Interpretations With Polynomial-Size Output_.**  
  Closely related MSO-interpretation perspective on polynomial-size output transformations.  
  DOI: https://doi.org/10.4230/LIPIcs.ICALP.2019.106  
  PDF: [BojanczykKieferLhote2019_String-to-String_Interpretations_With_Polynomial-Size_Output.pdf](pdfs/BojanczykKieferLhote2019_String-to-String_Interpretations_With_Polynomial-Size_Output.pdf)

- **Nathan Lhote (2020), _Pebble Minimization of Polyregular Functions_.**  
  Follow-up on quantitative structure of pebble resources for polyregular functions.  
  DOI: https://doi.org/10.1145/3373718.3394804  
  PDF: [Lhote2020_Pebble_Minimization_of_Polyregular_Functions.pdf](pdfs/Lhote2020_Pebble_Minimization_of_Polyregular_Functions.pdf)

## Local PDFs

The 82 PDFs currently stored here are:

- [pdfs/AhoHopcroftUllman1969_A_General_Theory_of_Translation.pdf](pdfs/AhoHopcroftUllman1969_A_General_Theory_of_Translation.pdf)
- [pdfs/AhoUllman1970_A_Characterization_of_Two-Way_Deterministic_Classes_of_Languages.pdf](pdfs/AhoUllman1970_A_Characterization_of_Two-Way_Deterministic_Classes_of_Languages.pdf)
- [pdfs/AlbertLawrence1985_A_Proof_of_Ehrenfeuchts_Conjecture.pdf](pdfs/AlbertLawrence1985_A_Proof_of_Ehrenfeuchts_Conjecture.pdf)
- [pdfs/AlurCerny2010_Expressiveness_of_Streaming_String_Transducers.pdf](pdfs/AlurCerny2010_Expressiveness_of_Streaming_String_Transducers.pdf)
- [pdfs/AlurCerny2011_Streaming_Transducers_for_Algorithmic_Verification_of_Single-Pass_List-Processing_Programs.pdf](pdfs/AlurCerny2011_Streaming_Transducers_for_Algorithmic_Verification_of_Single-Pass_List-Processing_Programs.pdf)
- [pdfs/AlurFreilichRaghothaman2014_Regular_Combinators_for_String_Transformations.pdf](pdfs/AlurFreilichRaghothaman2014_Regular_Combinators_for_String_Transformations.pdf)
- [pdfs/Baschenis2017_Untwisting_Two-Way_Transducers_in_Elementary_Time.pdf](pdfs/Baschenis2017_Untwisting_Two-Way_Transducers_in_Elementary_Time.pdf)
- [pdfs/BealLombardySakarovitch2006_Conjugacy_and_Equivalence_of_Weighted_Automata_and_Functional_Transducers.pdf](pdfs/BealLombardySakarovitch2006_Conjugacy_and_Equivalence_of_Weighted_Automata_and_Functional_Transducers.pdf)
- [pdfs/Benedikt2017_Polynomial_Automata_Zeroness_and_Applications.pdf](pdfs/Benedikt2017_Polynomial_Automata_Zeroness_and_Applications.pdf)
- [pdfs/Berstel1979_Transductions_and_Context-Free_Languages.pdf](pdfs/Berstel1979_Transductions_and_Context-Free_Languages.pdf)
- [pdfs/BerstelReutenauer1988_Rational_Series_and_Their_Languages.pdf](pdfs/BerstelReutenauer1988_Rational_Series_and_Their_Languages.pdf)
- [pdfs/BlattnerHead1977_Single-Valued_a-Transducers.pdf](pdfs/BlattnerHead1977_Single-Valued_a-Transducers.pdf)
- [pdfs/BloemEngelfriet2000_A_Comparison_of_Tree_Transductions_Defined_by_Monadic_Second_Order_Logic_and_by_Attribute_Grammars.pdf](pdfs/BloemEngelfriet2000_A_Comparison_of_Tree_Transductions_Defined_by_Monadic_Second_Order_Logic_and_by_Attribute_Grammars.pdf)
- [pdfs/Bojanczyk2014_Transducers_with_Origin_Information.pdf](pdfs/Bojanczyk2014_Transducers_with_Origin_Information.pdf)
- [pdfs/Bojanczyk2018_Polyregular_Functions.pdf](pdfs/Bojanczyk2018_Polyregular_Functions.pdf)
- [pdfs/Bojanczyk2019_The_Hilbert_Method_for_Transducer_Equivalence.pdf](pdfs/Bojanczyk2019_The_Hilbert_Method_for_Transducer_Equivalence.pdf)
- [pdfs/Bojanczyk2022_Transducers_of_polynomial_growth_preprint.pdf](pdfs/Bojanczyk2022_Transducers_of_polynomial_growth_preprint.pdf)
- [pdfs/Bojanczyk2023_On_the_growth_rates_of_polyregular_functions_preprint.pdf](pdfs/Bojanczyk2023_On_the_growth_rates_of_polyregular_functions_preprint.pdf)
- [pdfs/Bojanczyk2025_An_Automata_Toolbox.pdf](pdfs/Bojanczyk2025_An_Automata_Toolbox.pdf)
- [pdfs/BojanczykDaviaudKrishna2018_Regular_and_First-Order_List_Functions.pdf](pdfs/BojanczykDaviaudKrishna2018_Regular_and_First-Order_List_Functions.pdf)
- [pdfs/BojanczykDaviaudKrishna2018_Regular_and_First-Order_List_Functions_extended_arxiv.pdf](pdfs/BojanczykDaviaudKrishna2018_Regular_and_First-Order_List_Functions_extended_arxiv.pdf)
- [pdfs/BojanczykKieferLhote2019_String-to-String_Interpretations_With_Polynomial-Size_Output.pdf](pdfs/BojanczykKieferLhote2019_String-to-String_Interpretations_With_Polynomial-Size_Output.pdf)
- [pdfs/BojanczykStefanski2020_Single-Use_Automata_and_Transducers_for_Infinite_Alphabets.pdf](pdfs/BojanczykStefanski2020_Single-Use_Automata_and_Transducers_for_Infinite_Alphabets.pdf)
- [pdfs/Buchi1960_Weak_Second-Order_Arithmetic_and_Finite_Automata.pdf](pdfs/Buchi1960_Weak_Second-Order_Arithmetic_and_Finite_Automata.pdf)
- [pdfs/Choffrut1977_Une_caracterisation_des_fonctions_sequentielles.pdf](pdfs/Choffrut1977_Une_caracterisation_des_fonctions_sequentielles.pdf)
- [pdfs/ChytilJakl1977_Serial_Composition_of_2-Way_Finite-State_Transducers_and_Simple_Programs_on_Strings.pdf](pdfs/ChytilJakl1977_Serial_Composition_of_2-Way_Finite-State_Transducers_and_Simple_Programs_on_Strings.pdf)
- [pdfs/CourcelleEngelfriet2012_Graph_Structure_and_Monadic_Second-Order_Logic.pdf](pdfs/CourcelleEngelfriet2012_Graph_Structure_and_Monadic_Second-Order_Logic.pdf)
- [pdfs/CulikKarhumaki1983_Systems_of_Equations_over_a_Free_Monoid_and_Ehrenfeuchts_Conjecture.pdf](pdfs/CulikKarhumaki1983_Systems_of_Equations_over_a_Free_Monoid_and_Ehrenfeuchts_Conjecture.pdf)
- [pdfs/CulikSalomaa1978_On_the_Decidability_of_Homomorphism_Equivalence_for_Languages.pdf](pdfs/CulikSalomaa1978_On_the_Decidability_of_Homomorphism_Equivalence_for_Languages.pdf)
- [pdfs/Dubreil1941_Contribution_a_la_theorie_des_demi-groupes.pdf](pdfs/Dubreil1941_Contribution_a_la_theorie_des_demi-groupes.pdf)
- [pdfs/Eilenberg1974_Automata_Languages_and_Machines_Volume_A.pdf](pdfs/Eilenberg1974_Automata_Languages_and_Machines_Volume_A.pdf)
- [pdfs/EilenbergSchutzenberger1969_Rational_Sets_in_Commutative_Monoids.pdf](pdfs/EilenbergSchutzenberger1969_Rational_Sets_in_Commutative_Monoids.pdf)
- [pdfs/Elgot1961_Decision_Problems_of_Finite_Automata_Design_and_Related_Arithmetics.pdf](pdfs/Elgot1961_Decision_Problems_of_Finite_Automata_Design_and_Related_Arithmetics.pdf)
- [pdfs/ElgotMezei1965_On_Relations_Defined_by_Generalized_Finite_Automata.pdf](pdfs/ElgotMezei1965_On_Relations_Defined_by_Generalized_Finite_Automata.pdf)
- [pdfs/Engelfriet2015_Two-way_pebble_transducers_for_partial_functions_and_their_composition.pdf](pdfs/Engelfriet2015_Two-way_pebble_transducers_for_partial_functions_and_their_composition.pdf)
- [pdfs/EngelfrietHoogeboom2001_MSO_Definable_String_Transductions_and_Two-Way_Finite-State_Transducers.pdf](pdfs/EngelfrietHoogeboom2001_MSO_Definable_String_Transductions_and_Two-Way_Finite-State_Transducers.pdf)
- [pdfs/EngelfrietHoogeboomSamwel2007_XML_Transformation_by_Tree-Walking_Transducers_with_Invisible_Pebbles.pdf](pdfs/EngelfrietHoogeboomSamwel2007_XML_Transformation_by_Tree-Walking_Transducers_with_Invisible_Pebbles.pdf)
- [pdfs/EngelfrietManeth1999_Macro_Tree_Transducers_Attribute_Grammars_and_MSO_Definable_Tree_Translations.pdf](pdfs/EngelfrietManeth1999_Macro_Tree_Transducers_Attribute_Grammars_and_MSO_Definable_Tree_Translations.pdf)
- [pdfs/EngelfrietManeth2002_Two-Way_Finite_State_Transducers_with_Nested_Pebbles.pdf](pdfs/EngelfrietManeth2002_Two-Way_Finite_State_Transducers_with_Nested_Pebbles.pdf)
- [pdfs/FiliotReynierServais2013_From_Two-Way_to_One-Way_Finite_State_Transducers.pdf](pdfs/FiliotReynierServais2013_From_Two-Way_to_One-Way_Finite_State_Transducers.pdf)
- [pdfs/GinsburgRose1966.pdf](pdfs/GinsburgRose1966.pdf)
- [pdfs/GinsburgRose1966_A_Characterization_of_Machine_Mappings.pdf](pdfs/GinsburgRose1966_A_Characterization_of_Machine_Mappings.pdf)
- [pdfs/GlobermanHarel1996_Complexity_Results_for_Two-Way_and_Multi-Pebble_Automata.pdf](pdfs/GlobermanHarel1996_Complexity_Results_for_Two-Way_and_Multi-Pebble_Automata.pdf)
- [pdfs/Griffiths1968_The_Unsolvability_of_the_Equivalence_Problem_for_Lambda-Free_Nondeterministic_Generalized_Machines.pdf](pdfs/Griffiths1968_The_Unsolvability_of_the_Equivalence_Problem_for_Lambda-Free_Nondeterministic_Generalized_Machines.pdf)
- [pdfs/Gurari1982_The_Equivalence_Problem_for_Deterministic_Two-Way_Sequential_Transducers_is_Decidable.pdf](pdfs/Gurari1982_The_Equivalence_Problem_for_Deterministic_Two-Way_Sequential_Transducers_is_Decidable.pdf)
- [pdfs/HarjuKarhumaki1991_The_Equivalence_Problem_of_Multitape_Finite_Automata.pdf](pdfs/HarjuKarhumaki1991_The_Equivalence_Problem_of_Multitape_Finite_Automata.pdf)
- [pdfs/HopcroftUllman1967_An_Approach_to_a_Unified_Theory_of_Automata.pdf](pdfs/HopcroftUllman1967_An_Approach_to_a_Unified_Theory_of_Automata.pdf)
- [pdfs/Ibarra1971_Characterizations_of_Some_Tape_and_Time_Complexity_Classes.pdf](pdfs/Ibarra1971_Characterizations_of_Some_Tape_and_Time_Complexity_Classes.pdf)
- [pdfs/Kleene1951_Representation_of_Events_in_Nerve_Nets_and_Finite_Automata.pdf](pdfs/Kleene1951_Representation_of_Events_in_Nerve_Nets_and_Finite_Automata.pdf)
- [pdfs/KrohnRhodes1965_Algebraic_Theory_of_Machines_I.pdf](pdfs/KrohnRhodes1965_Algebraic_Theory_of_Machines_I.pdf)
- [pdfs/Lhote2020_Pebble_Minimization_of_Polyregular_Functions.pdf](pdfs/Lhote2020_Pebble_Minimization_of_Polyregular_Functions.pdf)
- [pdfs/McNaughtonPapert1971_Counter-Free_Automata.pdf](pdfs/McNaughtonPapert1971_Counter-Free_Automata.pdf)
- [pdfs/Mealy1955_Method_for_Synthesizing_Sequential_Circuits.pdf](pdfs/Mealy1955_Method_for_Synthesizing_Sequential_Circuits.pdf)
- [pdfs/Meyer1969_A_Note_on_Star-Free_Events.pdf](pdfs/Meyer1969_A_Note_on_Star-Free_Events.pdf)
- [pdfs/MiloSuciuVianu2003_Typechecking_for_XML_Transformers.pdf](pdfs/MiloSuciuVianu2003_Typechecking_for_XML_Transformers.pdf)
- [pdfs/Moore1956_Gedanken-Experiments_on_Sequential_Machines.pdf](pdfs/Moore1956_Gedanken-Experiments_on_Sequential_Machines.pdf)
- [pdfs/MurlakNiwinskiRytter2017_200_Problems_in_Formal_Languages_and_Automata_Theory.pdf](pdfs/MurlakNiwinskiRytter2017_200_Problems_in_Formal_Languages_and_Automata_Theory.pdf)
- [pdfs/MuschollPuppis2019_The_Many_Facets_of_String_Transducers.pdf](pdfs/MuschollPuppis2019_The_Many_Facets_of_String_Transducers.pdf)
- [pdfs/Nerode1958_Linear_Automaton_Transformations.pdf](pdfs/Nerode1958_Linear_Automaton_Transformations.pdf)
- [pdfs/Nguyen2024_Two_or_three_things_I_know_about_tree_transducers.pdf](pdfs/Nguyen2024_Two_or_three_things_I_know_about_tree_transducers.pdf)
- [pdfs/Nivat1968.pdf](pdfs/Nivat1968.pdf)
- [pdfs/Nivat1968_Transductions_des_langages_de_Chomsky.pdf](pdfs/Nivat1968_Transductions_des_langages_de_Chomsky.pdf)
- [pdfs/Pin2025_Mathematical_Foundations_of_Automata_Theory.pdf](pdfs/Pin2025_Mathematical_Foundations_of_Automata_Theory.pdf)
- [pdfs/Post1946_A_Variant_of_a_Recursively_Unsolvable_Problem.pdf](pdfs/Post1946_A_Variant_of_a_Recursively_Unsolvable_Problem.pdf)
- [pdfs/RabinScott1959_Finite_automata_and_their_decision_problems.pdf](pdfs/RabinScott1959_Finite_automata_and_their_decision_problems.pdf)
- [pdfs/ReutenauerSchutzenberger1991_Minimization_of_Rational_Word_Functions.pdf](pdfs/ReutenauerSchutzenberger1991_Minimization_of_Rational_Word_Functions.pdf)
- [pdfs/Sakarovitch2009_Elements_of_Automata_Theory.pdf](pdfs/Sakarovitch2009_Elements_of_Automata_Theory.pdf)
- [pdfs/Sakarovitch2021_Automata_and_Rational_Expressions.pdf](pdfs/Sakarovitch2021_Automata_and_Rational_Expressions.pdf)
- [pdfs/Schutzenberger1956_Une_theorie_algebrique_du_codage.pdf](pdfs/Schutzenberger1956_Une_theorie_algebrique_du_codage.pdf)
- [pdfs/Schutzenberger1961_A_Remark_on_Finite_Transducers.pdf](pdfs/Schutzenberger1961_A_Remark_on_Finite_Transducers.pdf)
- [pdfs/Schutzenberger1961_On_the_Definition_of_a_Family_of_Automata.pdf](pdfs/Schutzenberger1961_On_the_Definition_of_a_Family_of_Automata.pdf)
- [pdfs/Schutzenberger1965_On_Finite_Monoids_Having_Only_Trivial_Subgroups.pdf](pdfs/Schutzenberger1965_On_Finite_Monoids_Having_Only_Trivial_Subgroups.pdf)
- [pdfs/Schutzenberger1976_Sur_les_relations_rationnelles_entre_monoides_libres.pdf](pdfs/Schutzenberger1976_Sur_les_relations_rationnelles_entre_monoides_libres.pdf)
- [pdfs/Schutzenberger1976_Sur_les_relations_rationnelles_entre_monoides_libres_clean_scan.pdf](pdfs/Schutzenberger1976_Sur_les_relations_rationnelles_entre_monoides_libres_clean_scan.pdf)
- [pdfs/Schutzenberger2009_Oeuvres_completes_Tome_8.pdf](pdfs/Schutzenberger2009_Oeuvres_completes_Tome_8.pdf)
- [pdfs/Scott1967_Some_Definitional_Suggestions_for_Automata_Theory.pdf](pdfs/Scott1967_Some_Definitional_Suggestions_for_Automata_Theory.pdf)
- [pdfs/SeidlManethKemper2018_Equivalence_of_Deterministic_Top-Down_Tree-to-String_Transducers_Is_Decidable.pdf](pdfs/SeidlManethKemper2018_Equivalence_of_Deterministic_Top-Down_Tree-to-String_Transducers_Is_Decidable.pdf)
- [pdfs/Shepherdson1959_The_reduction_of_two-way_automata_to_one-way_automata.pdf](pdfs/Shepherdson1959_The_reduction_of_two-way_automata_to_one-way_automata.pdf)
- [pdfs/Sipser2012_Introduction_to_the_Theory_of_Computation.pdf](pdfs/Sipser2012_Introduction_to_the_Theory_of_Computation.pdf)
- [pdfs/Thomas1997_Languages_Automata_and_Logic.pdf](pdfs/Thomas1997_Languages_Automata_and_Logic.pdf)
- [pdfs/Trakhtenbrot1962_Konechnye_avtomaty_i_logika_odnomestnyh_predikatov.pdf](pdfs/Trakhtenbrot1962_Konechnye_avtomaty_i_logika_odnomestnyh_predikatov.pdf)
- [pdfs/Wilke1999_Classifying_Discrete_Temporal_Properties.pdf](pdfs/Wilke1999_Classifying_Discrete_Temporal_Properties.pdf)

`GinsburgRose1966.pdf` and `Nivat1968.pdf` are second copies of the two entries
directly below them; the long-named files are the ones the entries above link to.
