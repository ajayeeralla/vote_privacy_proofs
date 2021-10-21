# What is where
| Proofs | Coq file| Status |
|--------|----------|-------|
|core axioms|axioms| completed|
|axioms of FOO protocol |foo_axioms| completed but need to reflect latest changes|
|extended FuncApp| prop_17| completed|
|extend Fresh Ind| prop_16| needs to complete the proof|
| corrected version of prop from ESORICS paper| prop_13| completed|
| extended blindness| prop_21| completed|
| andb properties | prop_15| completed all except 15.2 (swapping branches)|
| cpa cca axioms| cpacca|









# Order of dependency
|File name|
|-----------|
|definitions.v|
|morphisms.v|
|cpdtTactics.v|
|induction.v|
|axioms.v|
|andbprops.v|
|ifTf.v|
|ifIdemp.v|
|ifMorph.v|
|indEq.v|
|ex71.v|
|eqm.v|
|ex11.v|
|ex74.v|
|eqBranch.v|
|eqCom.v|
|eqNonce.v|
|tactics.v|
|foo_axioms.v|
|prop1.v|

# Machine-checked Proofs of Vote Privacy using Computationally Complete Symbolic Attacker (CCSA)

We have formalized the proofs of vote privacy of the [FOO](https://link.springer.com/chapter/10.1007/3-540-57220-1_66) voting protocol presented in the paper using the [CCSA technique](https://dl.acm.org/doi/10.1145/2660267.2660276) in the [Coq proof assistant](https://coq.inria.fr/).

## Publication

This work can be seen as an extension of the stuff presented in the following paper:
* Gergei Bana, Rohit Chadha, and Ajay Kumar Eeralla. [Formal Analysis of Vote Privacy using Computationally Complete Symbolic Attacker](https://www.springerprofessional.de/en/formal-analysis-of-vote-privacy-using-computationally-complete-s/16013318), pp. 350-372, Computer Security: 23rd European Symposium on Research in Computer Security (ESORICS), Lecture Notes in Computer Science, Springer, September 2018.


## Prerequisites

* To compile the files, you will need to have installed Coq on your local machine.

### Installing

* To download and install Coq on your machine, click on the link [install coq](https://coq.inria.fr/download).

### Compiling the proofs

* To compile all the files simply type `make`

  [//]: # (It took about **15 mins** to compile all the files on the **Ubuntu 14.04 LTS** system with **Intel Core i5 3.20 GHz** processor and **8GiB RAM**)

* To compile a single file
  ```
  > coqc filename.v
  ```

[//]: # (To generate a new `Makefile` by typing)

  [//]: # (> coq_makefile -install none -I . *.v -o Makefile)


* HTML Coqdoc files can be generated by
  ```
  > coqdoc --html --toc --coqlib http://coq.inria.fr/stdlib/ -d _dirname_ *.v
  ```
* The directory webpages/coqdoc contains all the html files of the corresponding .v files

### `Note`
I have compiled the proofs using the Coq version [8.12.2](https://github.com/coq/coq/releases/tag/V8.12.2) on MacOS with memory 32 GB.

## Author

* **Ajay Kumar Eeralla** --University of Missouri-Columbia

## Copy Right Information
Copyright (c) 2017-2021, Ajay Kumar Eeralla <ae266@mail.missouri.edu>, University of Missouri-Columbia, USA