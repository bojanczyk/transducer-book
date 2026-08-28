# Literature for Parts A-D

This folder collects the main sources to cite for the first four parts of the book.

BibTeX entries for everything listed here live in the book's bibliography, [../bib.bib](../bib.bib).

## Background

- **S. C. Kleene (1951), _Representation of Events in Nerve Nets and Finite Automata_.**  
  The origin of regular expressions and of the Kleene Theorem, which underlies the rational/recognisable material in Part B and the regular languages used throughout. Written as a RAND research memorandum, and freely available in that form; the revised version appeared in _Automata Studies_ (Shannon and McCarthy, eds.), Annals of Mathematics Studies 34, Princeton University Press, 1956, pp. 3-41.  
  RAND: https://www.rand.org/pubs/research_memoranda/RM704.html (report RM-704)  
  PDF: [Kleene1951_Representation_of_Events_in_Nerve_Nets_and_Finite_Automata.pdf](pdfs/Kleene1951_Representation_of_Events_in_Nerve_Nets_and_Finite_Automata.pdf) (RAND memorandum)

- **Jean-Éric Pin (2025), _Mathematical Foundations of Automata Theory_ (MPRI lecture notes).**  
  General algebraic-automata-theory reference: semigroups, Green's relations, recognisable and rational sets, star-free and piecewise testable languages, varieties. The profinite material is **Chapter X, _Profinite words_, pp. 175-188** — profinite metric and topology (§2.1), free profinite monoid and its universal property (§2.2-2.3), ω-terms (§2.4), recognisable languages as clopen sets (§3).  
  Link: https://www.irif.fr/~jep/PDF/MPRI/MPRI.pdf  
  PDF: [Pin2025_Mathematical_Foundations_of_Automata_Theory.pdf](pdfs/Pin2025_Mathematical_Foundations_of_Automata_Theory.pdf) (version of 24 March 2025, 344 pp.)  
  Note: a living document, so quote the version date when citing. It is also cited in the literature as [Pin22], which is the version of 18 February 2022; Chapter X sits at pp. 175-188 in both.

- **Damian Niwiński and Wojciech Rytter, edited by Filip Murlak (2017), _200 Problems in Formal Languages and Automata Theory_.**  
  Problem collection used for classical exercises. The book is cited in the text as the Cambridge University Press edition, _200 Problems on Languages, Automata, and Computation_ (2023, DOI [10.1017/9781009072632](https://doi.org/10.1017/9781009072632)); the PDF stored here is the **earlier University of Warsaw 2017 edition**, problems only, without solutions.  
  PDF: [MurlakNiwinskiRytter2017_200_Problems_in_Formal_Languages_and_Automata_Theory.pdf](pdfs/MurlakNiwinskiRytter2017_200_Problems_in_Formal_Languages_and_Automata_Theory.pdf) (University of Warsaw 2017, 65 pp.)  
  Warning: problem numbering differs between the two editions. In this 2017 edition, Problem 24 is the one about reversal, Problem 30 is Root/Sqrt/Log/Fibb, and Problem 35 is about counting factors — so the pinpoint `Problems 30 and 35` used in the text follows the 2023 numbering, not this file.

## Part A — Mealy machines

- **George H. Mealy (1955), _A Method for Synthesizing Sequential Circuits_.**  
  Origin paper for Mealy machines and letter-to-letter transducers.  
  DOI: https://doi.org/10.1002/j.1538-7305.1955.tb03788.x  
  PDF: [Mealy1955_Method_for_Synthesizing_Sequential_Circuits.pdf](pdfs/Mealy1955_Method_for_Synthesizing_Sequential_Circuits.pdf)

- **Kenneth Krohn and John Rhodes (1965), _Algebraic Theory of Machines. I. Prime Decomposition Theorem for Finite Semigroups and Machines_.**  
  The classical decomposition theorem behind the book’s Krohn-Rhodes chapter.  
  DOI: https://doi.org/10.1090/S0002-9947-1965-0188316-1  
  PDF: [KrohnRhodes1965_Algebraic_Theory_of_Machines_I.pdf](pdfs/KrohnRhodes1965_Algebraic_Theory_of_Machines_I.pdf)

- **Albert R. Meyer (1969), _A Note on Star-Free Events_.**  
  Short proof that the star-free languages are exactly the group-free (aperiodic) ones, obtained by appealing to the Krohn-Rhodes decomposition theorem above. Background for the aperiodic Mealy machines of the Krohn-Rhodes chapter.  
  DOI: https://doi.org/10.1145/321510.321513  
  PDF: [Meyer1969_A_Note_on_Star-Free_Events.pdf](pdfs/Meyer1969_A_Note_on_Star-Free_Events.pdf)

- **Thomas Wilke (1999), _Classifying Discrete Temporal Properties_.**  
  Survey of the classification of temporal properties, and of the methods behind it, with the connections to finite automata and to the theory of finite semigroups.  
  DOI: https://doi.org/10.1007/3-540-49116-3_3  
  PDF: [Wilke1999_Classifying_Discrete_Temporal_Properties.pdf](pdfs/Wilke1999_Classifying_Discrete_Temporal_Properties.pdf)

- **Samuel Eilenberg (1976), _Automata, Languages, and Machines. Volume B_.**  
  The standard algebraic treatment of machines: wreath products, the Krohn-Rhodes decomposition, and the variety theory relating pseudovarieties of finite monoids to classes of languages. Includes two chapters by Bret Tilson on the depth decomposition theorem and on complexity. Companion to Volume A, listed under Part B below.  
  Publisher: https://shop.elsevier.com/books/automata-languages-and-machines/eilenberg/978-0-12-234002-4  
  Borrowable scan: https://archive.org/details/automatalanguage0000eile  
  No PDF stored locally (in copyright, no free electronic edition).

## Part B — Rational relations and functions

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

- **Paul Dubreil (1941), _Contribution à la théorie des demi-groupes. I_.**  
  Origin of right congruences in semigroup theory, the algebraic background to the Myhill-Nerode chapter. Page 8 has the definition of a right congruence, and Theorem 3 says that the relation defined there is one. Mémoires de l'Académie des Sciences de l'Institut de France, tome 63, pp. 1-52.  
  Gallica (BnF) has tome 63 digitised as ark `bpt6k3278g`; the memoir is no. 3 of the volume and occupies views 355-406, which are its pages 1-52.  
  Gallica: https://gallica.bnf.fr/ark:/12148/bpt6k3278g/f355  
  PDF: [Dubreil1941_Contribution_a_la_theorie_des_demi-groupes.pdf](pdfs/Dubreil1941_Contribution_a_la_theorie_des_demi-groupes.pdf) (assembled from the Gallica page scans; the volume has no OCR layer)  
  Note: likely still in copyright (Dubreil died 1994), and Gallica marks the volume as `sous droits`.

- **M.-P. Schützenberger (1955-1956), _Une théorie algébrique du codage_.**  
  The talk in which Schützenberger set out his algebraic approach to codes, the starting point for the line of work continued in his later papers on transducers and rational relations. Séminaire Dubreil, tome 9, exposé no. 15, 24 pages.  
  Numdam: https://www.numdam.org/item/SD_1955-1956__9__A10_0/  
  PDF: [Schutzenberger1956_Une_theorie_algebrique_du_codage.pdf](pdfs/Schutzenberger1956_Une_theorie_algebrique_du_codage.pdf)

- **M. P. Schützenberger (1961), _A Remark on Finite Transducers_.**  
  Classic finite-transducer reference, especially relevant to the deterministic/function side.  
  DOI: https://doi.org/10.1016/S0019-9958(61)80006-5  
  PDF: [Schutzenberger1961_A_Remark_on_Finite_Transducers.pdf](pdfs/Schutzenberger1961_A_Remark_on_Finite_Transducers.pdf)

- **M. P. Schützenberger (1976), _Sur les relations rationnelles entre monoïdes libres_.**  
  Directly on rational relations over free monoids.  
  DOI: https://doi.org/10.1016/0304-3975(76)90026-8  
  PDF: [Schutzenberger1976_Sur_les_relations_rationnelles_entre_monoides_libres.pdf](pdfs/Schutzenberger1976_Sur_les_relations_rationnelles_entre_monoides_libres.pdf)

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

- **Jean Berstel (1979), _Transductions and Context-Free Languages_.**  
  The standard monograph on rational transductions; the free 2009 electronic edition covers the first four chapters, including the general theory of rational transductions.  
  Link: https://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions14dec2009.pdf  
  PDF: [Berstel1979_Transductions_and_Context-Free_Languages.pdf](pdfs/Berstel1979_Transductions_and_Context-Free_Languages.pdf) (electronic edition, 14 Dec 2009)

- **Christian Choffrut (1977), _Une caractérisation des fonctions séquentielles et des fonctions sous-séquentielles en tant que relations rationnelles_.**  
  Key paper on sequential/subsequential functions as rational relations.  
  DOI: https://doi.org/10.1016/0304-3975(77)90049-4  
  PDF: [Choffrut1977_Une_caracterisation_des_fonctions_sequentielles.pdf](pdfs/Choffrut1977_Une_caracterisation_des_fonctions_sequentielles.pdf)

- **Marie-Pierre Béal, Sylvain Lombardy, and Jacques Sakarovitch (2006), _Conjugacy and Equivalence of Weighted Automata and Functional Transducers_.**  
  Useful for the weighted-automata route to equivalence of rational functions.  
  DOI: https://doi.org/10.1007/11753728_9  
  PDF: [BealLombardySakarovitch2006_Conjugacy_and_Equivalence_of_Weighted_Automata_and_Functional_Transducers.pdf](pdfs/BealLombardySakarovitch2006_Conjugacy_and_Equivalence_of_Weighted_Automata_and_Functional_Transducers.pdf)

- **Michael Benedikt, Timothy Duff, Aditya Sharad, and James Worrell (2017), _Polynomial Automata: Zeroness and Applications_.**  
  The paper that introduces polynomial automata, as a generalisation of weighted automata over a field, and settles the complexity of the Zeroness Problem for them: non-primitive recursive in general, primitive recursive for a subclass. Relevant to the weighted-automata chapter.  
  DOI: https://doi.org/10.1109/LICS.2017.8005101  
  PDF: [Benedikt2017_Polynomial_Automata_Zeroness_and_Applications.pdf](pdfs/Benedikt2017_Polynomial_Automata_Zeroness_and_Applications.pdf) (author copy, Oxford Research Archive)

## Part C — Regular functions

- **Michael O. Rabin and Dana Scott (1959), _Finite Automata and Their Decision Problems_.**  
  Classic source for two-way vs one-way automata background used in regular transducer proofs.  
  DOI: https://doi.org/10.1147/rd.32.0114  
  PDF: [RabinScott1959_Finite_automata_and_their_decision_problems.pdf](pdfs/RabinScott1959_Finite_automata_and_their_decision_problems.pdf)

- **J. C. Shepherdson (1959), _The Reduction of Two-Way Automata to One-Way Automata_.**  
  Independent two-way-to-one-way reduction; historically relevant for the two-way transducer viewpoint.  
  DOI: https://doi.org/10.1147/rd.32.0198  
  PDF: [Shepherdson1959_The_reduction_of_two-way_automata_to_one-way_automata.pdf](pdfs/Shepherdson1959_The_reduction_of_two-way_automata_to_one-way_automata.pdf)

- **J. E. Hopcroft and J. D. Ullman (1967), _An Approach to a Unified Theory of Automata_.**  
  Early decomposition-style techniques related to crossing-sequence arguments in this part.  
  DOI: https://doi.org/10.1109/FOCS.1967.4  
  PDF: [HopcroftUllman1967_An_Approach_to_a_Unified_Theory_of_Automata.pdf](pdfs/HopcroftUllman1967_An_Approach_to_a_Unified_Theory_of_Automata.pdf)

- **Mikołaj Bojańczyk (2025), _An Automata Toolbox_.**  
  Modern lecture-note reference used repeatedly for regular-transducer arguments and proofs.  
  Link: https://www.mimuw.edu.pl/~bojan/paper/automata-toolbox-book  
  PDF: [Bojanczyk2025_An_Automata_Toolbox.pdf](pdfs/Bojanczyk2025_An_Automata_Toolbox.pdf) (version of 30 December 2025, 293 pp.)  
  Note: a living document; dated versions are kept alongside it at mimuw.edu.pl/~bojan/papers/.

### SST and MSO transductions (Part C focus)

- **Rajeev Alur and Pavol Černý (2010), _Expressiveness of Streaming String Transducers_.**  
  Core SST paper: defines the model and connects it to regular string-to-string transductions.  
  Link: https://arxiv.org/abs/1002.4700

- **Rajeev Alur and Pavol Černý (2011), _Streaming Transducers for Algorithmic Verification of Single-Pass List-Processing Programs_.**  
  Foundational verification-oriented SST perspective, with strong algorithmic motivations.  
  DOI: https://doi.org/10.1145/1926385.1926454  
  PDF: [AlurCerny2011_Streaming_Transducers_for_Algorithmic_Verification_of_Single-Pass_List-Processing_Programs.pdf](pdfs/AlurCerny2011_Streaming_Transducers_for_Algorithmic_Verification_of_Single-Pass_List-Processing_Programs.pdf)

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

- **Mikołaj Bojańczyk (2014), _Transducers with Origin Information_.**  
  Origin semantics viewpoint that clarifies and unifies regular string transducer models.  
  Link: https://doi.org/10.1007/978-3-662-43951-7_10  
  PDF: [Bojanczyk2014_Transducers_with_Origin_Information.pdf](pdfs/Bojanczyk2014_Transducers_with_Origin_Information.pdf)

- **Félix Baschenis, Olivier Gauwin, Anca Muscholl, and Gabriele Puppis (2017), _Untwisting Two-Way Transducers in Elementary Time_.**  
  Elementary-complexity algorithm for deciding one-way definability of a two-way transducer, and for sweeping transducers; sharpens the Filiot-Reynier-Servais result above.  
  DOI: https://doi.org/10.1109/LICS.2017.8005138  
  PDF: [Baschenis2017_Untwisting_Two-Way_Transducers_in_Elementary_Time.pdf](pdfs/Baschenis2017_Untwisting_Two-Way_Transducers_in_Elementary_Time.pdf)

- **Anca Muscholl and Gabriele Puppis (2019), _The Many Facets of String Transducers (Invited Talk)_.**  
  Compact survey of equivalent regular transducer models (two-way, SST, MSO, and related viewpoints).  
  DOI: https://doi.org/10.4230/LIPIcs.STACS.2019.2  
  PDF: [MuschollPuppis2019_The_Many_Facets_of_String_Transducers.pdf](pdfs/MuschollPuppis2019_The_Many_Facets_of_String_Transducers.pdf)

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

- **Oscar H. Ibarra (1971), _Characterizations of Some Tape and Time Complexity Classes of Turing Machines in Terms of Multihead and Auxiliary Stack Automata_.**  
  Multihead automata correspond to logarithmic space; the reference for what pebble transducers would become without the stack discipline.  
  DOI: https://doi.org/10.1016/S0022-0000(71)80029-6  
  PDF: [Ibarra1971_Characterizations_of_Some_Tape_and_Time_Complexity_Classes.pdf](pdfs/Ibarra1971_Characterizations_of_Some_Tape_and_Time_Complexity_Classes.pdf)

- **Noa Lewenstein and David Harel (1996), _Complexity Results for Two-Way and Multi-Pebble Automata and their Logics_.**  
  Foundational complexity background for pebble-style models and stack-discipline discussions.  
  DOI: https://doi.org/10.1016/S0304-3975(96)00119-3  
  PDF: [LewensteinHarel1996_Complexity_Results_for_Two-Way_and_Multi-Pebble_Automata.pdf](pdfs/LewensteinHarel1996_Complexity_Results_for_Two-Way_and_Multi-Pebble_Automata.pdf)

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

The PDFs currently stored here are:

- [pdfs/Meyer1969_A_Note_on_Star-Free_Events.pdf](pdfs/Meyer1969_A_Note_on_Star-Free_Events.pdf)
- [pdfs/Wilke1999_Classifying_Discrete_Temporal_Properties.pdf](pdfs/Wilke1999_Classifying_Discrete_Temporal_Properties.pdf)
- [pdfs/Bojanczyk2018_Polyregular_Functions.pdf](pdfs/Bojanczyk2018_Polyregular_Functions.pdf)
- [pdfs/EngelfrietManeth2002_Two-Way_Finite_State_Transducers_with_Nested_Pebbles.pdf](pdfs/EngelfrietManeth2002_Two-Way_Finite_State_Transducers_with_Nested_Pebbles.pdf)
- [pdfs/MurlakNiwinskiRytter2017_200_Problems_in_Formal_Languages_and_Automata_Theory.pdf](pdfs/MurlakNiwinskiRytter2017_200_Problems_in_Formal_Languages_and_Automata_Theory.pdf)
- [pdfs/Baschenis2017_Untwisting_Two-Way_Transducers_in_Elementary_Time.pdf](pdfs/Baschenis2017_Untwisting_Two-Way_Transducers_in_Elementary_Time.pdf)
- [pdfs/Bojanczyk2025_An_Automata_Toolbox.pdf](pdfs/Bojanczyk2025_An_Automata_Toolbox.pdf)
- [pdfs/EngelfrietHoogeboomSamwel2007_XML_Transformation_by_Tree-Walking_Transducers_with_Invisible_Pebbles.pdf](pdfs/EngelfrietHoogeboomSamwel2007_XML_Transformation_by_Tree-Walking_Transducers_with_Invisible_Pebbles.pdf)
- [pdfs/HopcroftUllman1967_An_Approach_to_a_Unified_Theory_of_Automata.pdf](pdfs/HopcroftUllman1967_An_Approach_to_a_Unified_Theory_of_Automata.pdf)
- [pdfs/Ibarra1971_Characterizations_of_Some_Tape_and_Time_Complexity_Classes.pdf](pdfs/Ibarra1971_Characterizations_of_Some_Tape_and_Time_Complexity_Classes.pdf)
- [pdfs/LewensteinHarel1996_Complexity_Results_for_Two-Way_and_Multi-Pebble_Automata.pdf](pdfs/LewensteinHarel1996_Complexity_Results_for_Two-Way_and_Multi-Pebble_Automata.pdf)
- [pdfs/MiloSuciuVianu2003_Typechecking_for_XML_Transformers.pdf](pdfs/MiloSuciuVianu2003_Typechecking_for_XML_Transformers.pdf)
- [pdfs/Benedikt2017_Polynomial_Automata_Zeroness_and_Applications.pdf](pdfs/Benedikt2017_Polynomial_Automata_Zeroness_and_Applications.pdf)
- [pdfs/Pin2025_Mathematical_Foundations_of_Automata_Theory.pdf](pdfs/Pin2025_Mathematical_Foundations_of_Automata_Theory.pdf)
- [pdfs/Eilenberg1974_Automata_Languages_and_Machines_Volume_A.pdf](pdfs/Eilenberg1974_Automata_Languages_and_Machines_Volume_A.pdf)
- [pdfs/Dubreil1941_Contribution_a_la_theorie_des_demi-groupes.pdf](pdfs/Dubreil1941_Contribution_a_la_theorie_des_demi-groupes.pdf)
- [pdfs/Schutzenberger1956_Une_theorie_algebrique_du_codage.pdf](pdfs/Schutzenberger1956_Une_theorie_algebrique_du_codage.pdf)
- [pdfs/Kleene1951_Representation_of_Events_in_Nerve_Nets_and_Finite_Automata.pdf](pdfs/Kleene1951_Representation_of_Events_in_Nerve_Nets_and_Finite_Automata.pdf)
- [pdfs/Mealy1955_Method_for_Synthesizing_Sequential_Circuits.pdf](pdfs/Mealy1955_Method_for_Synthesizing_Sequential_Circuits.pdf)
- [pdfs/KrohnRhodes1965_Algebraic_Theory_of_Machines_I.pdf](pdfs/KrohnRhodes1965_Algebraic_Theory_of_Machines_I.pdf)
- [pdfs/ElgotMezei1965_On_Relations_Defined_by_Generalized_Finite_Automata.pdf](pdfs/ElgotMezei1965_On_Relations_Defined_by_Generalized_Finite_Automata.pdf)
- [pdfs/GinsburgRose1966_A_Characterization_of_Machine_Mappings.pdf](pdfs/GinsburgRose1966_A_Characterization_of_Machine_Mappings.pdf)
- [pdfs/Nivat1968_Transductions_des_langages_de_Chomsky.pdf](pdfs/Nivat1968_Transductions_des_langages_de_Chomsky.pdf)
- [pdfs/Schutzenberger1961_A_Remark_on_Finite_Transducers.pdf](pdfs/Schutzenberger1961_A_Remark_on_Finite_Transducers.pdf)
- [pdfs/Schutzenberger1976_Sur_les_relations_rationnelles_entre_monoides_libres.pdf](pdfs/Schutzenberger1976_Sur_les_relations_rationnelles_entre_monoides_libres.pdf)
- [pdfs/Choffrut1977_Une_caracterisation_des_fonctions_sequentielles.pdf](pdfs/Choffrut1977_Une_caracterisation_des_fonctions_sequentielles.pdf)
- [pdfs/Berstel1979_Transductions_and_Context-Free_Languages.pdf](pdfs/Berstel1979_Transductions_and_Context-Free_Languages.pdf)
- [pdfs/RabinScott1959_Finite_automata_and_their_decision_problems.pdf](pdfs/RabinScott1959_Finite_automata_and_their_decision_problems.pdf)
- [pdfs/Shepherdson1959_The_reduction_of_two-way_automata_to_one-way_automata.pdf](pdfs/Shepherdson1959_The_reduction_of_two-way_automata_to_one-way_automata.pdf)
- [pdfs/AlurCerny2011_Streaming_Transducers_for_Algorithmic_Verification_of_Single-Pass_List-Processing_Programs.pdf](pdfs/AlurCerny2011_Streaming_Transducers_for_Algorithmic_Verification_of_Single-Pass_List-Processing_Programs.pdf)
- [pdfs/EngelfrietHoogeboom2001_MSO_Definable_String_Transductions_and_Two-Way_Finite-State_Transducers.pdf](pdfs/EngelfrietHoogeboom2001_MSO_Definable_String_Transductions_and_Two-Way_Finite-State_Transducers.pdf)
- [pdfs/FiliotReynierServais2013_From_Two-Way_to_One-Way_Finite_State_Transducers.pdf](pdfs/FiliotReynierServais2013_From_Two-Way_to_One-Way_Finite_State_Transducers.pdf)
- [pdfs/Bojanczyk2014_Transducers_with_Origin_Information.pdf](pdfs/Bojanczyk2014_Transducers_with_Origin_Information.pdf)
- [pdfs/Engelfriet2015_Two-way_pebble_transducers_for_partial_functions_and_their_composition.pdf](pdfs/Engelfriet2015_Two-way_pebble_transducers_for_partial_functions_and_their_composition.pdf)
- [pdfs/Lhote2020_Pebble_Minimization_of_Polyregular_Functions.pdf](pdfs/Lhote2020_Pebble_Minimization_of_Polyregular_Functions.pdf)
- [pdfs/BealLombardySakarovitch2006_Conjugacy_and_Equivalence_of_Weighted_Automata_and_Functional_Transducers.pdf](pdfs/BealLombardySakarovitch2006_Conjugacy_and_Equivalence_of_Weighted_Automata_and_Functional_Transducers.pdf)
- [pdfs/CourcelleEngelfriet2012_Graph_Structure_and_Monadic_Second-Order_Logic.pdf](pdfs/CourcelleEngelfriet2012_Graph_Structure_and_Monadic_Second-Order_Logic.pdf)
- [pdfs/BojanczykKieferLhote2019_String-to-String_Interpretations_With_Polynomial-Size_Output.pdf](pdfs/BojanczykKieferLhote2019_String-to-String_Interpretations_With_Polynomial-Size_Output.pdf)
- [pdfs/MuschollPuppis2019_The_Many_Facets_of_String_Transducers.pdf](pdfs/MuschollPuppis2019_The_Many_Facets_of_String_Transducers.pdf)
- [pdfs/Bojanczyk2022_Transducers_of_polynomial_growth_preprint.pdf](pdfs/Bojanczyk2022_Transducers_of_polynomial_growth_preprint.pdf)
