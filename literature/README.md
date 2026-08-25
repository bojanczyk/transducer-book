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

## Part A — Mealy machines

- **George H. Mealy (1955), _A Method for Synthesizing Sequential Circuits_.**  
  Origin paper for Mealy machines and letter-to-letter transducers.  
  DOI: https://doi.org/10.1002/j.1538-7305.1955.tb03788.x  
  PDF: [Mealy1955_Method_for_Synthesizing_Sequential_Circuits.pdf](pdfs/Mealy1955_Method_for_Synthesizing_Sequential_Circuits.pdf)

- **Kenneth Krohn and John Rhodes (1965), _Algebraic Theory of Machines. I. Prime Decomposition Theorem for Finite Semigroups and Machines_.**  
  The classical decomposition theorem behind the book’s Krohn-Rhodes chapter.  
  DOI: https://doi.org/10.1090/S0002-9947-1965-0188316-1  
  PDF: [KrohnRhodes1965_Algebraic_Theory_of_Machines_I.pdf](pdfs/KrohnRhodes1965_Algebraic_Theory_of_Machines_I.pdf)

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
  Link: https://dblp.org/rec/conf/swat/HopcroftU67

- **Mikołaj Bojańczyk (2025), _An Automata Toolbox_.**  
  Modern lecture-note reference used repeatedly for regular-transducer arguments and proofs.  
  Link: https://www.mimuw.edu.pl/~bojan/paper/automata-toolbox-book

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

- **Anca Muscholl and Gabriele Puppis (2019), _The Many Facets of String Transducers (Invited Talk)_.**  
  Compact survey of equivalent regular transducer models (two-way, SST, MSO, and related viewpoints).  
  DOI: https://doi.org/10.4230/LIPIcs.STACS.2019.2  
  PDF: [MuschollPuppis2019_The_Many_Facets_of_String_Transducers.pdf](pdfs/MuschollPuppis2019_The_Many_Facets_of_String_Transducers.pdf)

## Part D — Polyregular functions

- **Mikołaj Bojańczyk (2018), _Polyregular Functions_.**  
  Main reference introducing polyregular functions and key equivalent models.  
  Link: https://arxiv.org/abs/1810.08760

- **Mikołaj Bojańczyk (2022), _Transducers of Polynomial Growth_.**  
  LICS paper developing the polynomial-growth perspective for string transductions.  
  DOI: https://doi.org/10.1145/3531130.3533326  
  DBLP: https://dblp.org/rec/conf/lics/Bojanczyk22  
  PDF: [Bojanczyk2022_Transducers_of_polynomial_growth_preprint.pdf](pdfs/Bojanczyk2022_Transducers_of_polynomial_growth_preprint.pdf) (author preprint)

- **Noa Lewenstein and David Harel (1996), _Complexity Results for Two-Way and Multi-Pebble Automata and their Logics_.**  
  Foundational complexity background for pebble-style models and stack-discipline discussions.  
  Link: https://dblp.org/rec/journals/tcs/LewensteinH96

- **Tova Milo, Dan Suciu, and Victor Vianu (2003), _Typechecking for XML Transformers_.**  
  Introduces pebble-transducer machinery in the XML-transformation setting.  
  Link: https://dblp.org/rec/journals/jcss/MiloSV03

- **Joost Engelfriet and Sebastian Maneth (2002), _Two-Way Finite State Transducers with Nested Pebbles_.**  
  Important bridge between nested-pebble transducers and string/tree transduction formalisms.  
  Link: https://dblp.org/rec/conf/mfcs/EngelfrietM02

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
