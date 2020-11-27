## KeYPR

**Proof Repositories for Correct-by-Construction Software Product Lines**

This is a frontend to the [KeY verification system](http://key-project.org) [[1]](#references) for efficiently proving the correctness of *correct-by-construction software product lines* as described in my master thesis [[2]](#references).

*Correctness-by-construction* (CbC) [[3]](#references) is a methodology to systematically derive correct programs from a given specification.
*Correct-by-construction software product lines* [[4]](#references) apply the CbC methodology to software product lines (SPLs), which are large families of programs that share a common set of features.
On a technical level, the correct application of CbC refinement rules can be enforced with the KeY verification system for individual products of an SPL [[5]](#references).
However, to check an entire SPL, this approach checks all its product individually, which is inefficient for large SPLs (product-based analysis).

With our approach as implemented in KeYPR, we can avoid checking each product of an SPL in isolation.
To do this, we use *proof repositories*, which cache proofs systematically so that we can reuse them for several configurations of an SPL.
This is the first automated implementation of proof repositories, which have been described in theory before [[6]](#references).
With KeYPR, we focus on the application of proof repositories to correct-by-construction SPLs, although traditional post-hoc verification can also benefit from proof repositories.

### The Gist

- We provide the case study and evaluation results described in the thesis in the `evaluation` directory.
- We use a modified KeY 2.7 version (in the `lib` directory, source code available [here](https://git.key-project.org/key/key/-/commits/kuiterAbstractContracts)) with support abstract contracts [7].
- The proof repository core and shell of KeYPR are implemented in the Lisp dialect Clojure (see `src/main/clojure/de/ovgu/spldev/keypr.clj`), which allows us to closely follow the definitions from the thesis.
- The interface to KeY, programming model, and Java code generator are implemented in Java (see `src/main/java/de/ovgu/spldev/keypr`).
- A pre-built and self-contained JAR file is available in the `evaluation` directory.
  Run `java -jar KeYPR.jar repl` to start an interactive REPL. Consult `case-study.clj` for an example usage.
  You can also pass a file on the command line to evaluate it (e.g., `java -jar KeYPR.jar case-study.clj`).
  If the file suffix is `.java`, `.key`, or `.proof`, the file is loaded into the KeY graphical user interface.
  Alternatively, you can also load the user interface by evaluating `(key!)` inside the REPL.
- For a manual build, the only dependency required is [JDK 1.8](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html).
  You can build the JAR by running `./gradlew build`, which stores the JAR file into `build/libs`.
  Alternatively, you can directly run the JAR with `./gradlew run` or start an NREPL server on port 55555 for debugging with `./gradlew clojureRepl`.
- You can use the project with [IntelliJ IDEA](https://www.jetbrains.com/idea/) / [Cursive IDE](https://cursive-ide.com/).
  Create an `Application` run configuration to run the JAR.
  Alternatively, use `Execute Gradle Task` to run the `clojureRepl` task, then create and run a `Clojure REPL > Remote` run configuration to use the Cursive REPL.
  You can then load `keypr.clj` into the REPL by opening it, running `Load File in REPL` (or pressing `Alt+Shift+L`), and evaluating `(ns de.ovgu.spldev.keypr.core)`.

### License

This project is a research effort of the [DBSE working group](http://www.dbse.ovgu.de/).
It is released under the [LGPL v3 license](LICENSE.txt).
Feel free to [contact me](mailto:kuiter@ovgu.de) (the main developer) if you have any questions.

### References

1. Wolfgang Ahrendt, Bernhard Beckert; Richard Bubel; Reiner Hähnle; Peter H. Schmitt, and Mattias Ulbrich. 2016. [Deductive Software Verification - The KeY Book - From Theory to Practice](https://www.key-project.org/thebook2/). Springer.
2. Elias Kuiter. 2020. Proof Repositories for Correct-by-Construction Software Product Lines. Otto-von-Guericke-University Magdeburg. 
3. Derrick G. Kourie and Bruce W. Watson. 2014. [The Correctness-by-Construction Approach to Programming](https://www.springerprofessional.de/the-correctness-by-construction-approach-to-programming/3827484). Springer Publishing Company, Incorporated.
4. Tabea Bordis, Tobias Runge, Alexander Knüppel, Thomas Thüm, and Ina Schaefer. 2020. [Variational correctness-by-construction](https://dl.acm.org/doi/abs/10.1145/3377024.3377038). Working Conference on Variability Modelling of Software-Intensive Systems. 
5. Tobias Runge, Ina Schaefer, Loek Cleophas, Thomas Thüm, Derrick G. Kourie, and Bruce W. Watson. 2019. Tool Support for Correctness-by-Construction. International Conference on Fundamental Approaches to Software Engineering. 
6. Richard Bubel, Ferruccio Damiani, Reiner Hähnle, Einar Broch Johnsen, Olaf Owe, Ina Schaefer, and Ingrid Chieh Yu. 2016. [Proof Repositories for Compositional Verification of Evolving Software Systems](https://link.springer.com/chapter/10.1007/978-3-319-46508-1_8). Transactions on Foundations for Mastering Change.
7. Richard Bubel, Reiner Hähnle, and Maria Pelevina. 2014. [Fully Abstract Operation Contracts](https://link.springer.com/chapter/10.1007/978-3-662-45231-8_9). International Symposium On Leveraging Applications of Formal Methods, Verification and Validation.