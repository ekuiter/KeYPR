(comment (ns de.ovgu.spldev.keypr
           "KeYPR: KeY for Proof Repositories
           Copyright (c) Elias Kuiter 2020"
           (:use [clojure.set :only (union difference subset?)]
                 [clojure.string :as s :only (join starts-with? ends-with? split lower-case)])
           (:import (de.ovgu.spldev.keypr Signature$Field Signature$Method Utils$Pair Signature$Call
                                          Program Program$Klass Program$Field Program$Implementation
                                          Program$Call Program$Binding Program$ProofDescriptor Program$Setting
                                          Program$BeginProof Program$ContinueProof Program$ProofRepository
                                          Macro KeYBridge VerificationSystem Utils CodeGenerator Evaluation)
                    (java.io File)
                    (org.pmw.tinylog Logger Configurator Level)
                    (java.time Instant Duration)))

         ;;; Definition 3.8: External Signatures
         (defn original-signature [M] (erase-names (signature (-> M :S :type) (-> M :S :name) "original" (-> M :S :ps))))
         (defn method-signature [M H] (let [[_ _ [l-type _] m as] (H :s)] (erase-names (signature l-type (-> M :S :name) m as))))
         (defn original? [chi] (and chi (not= (s/replace chi #"original_(pre|post)\((.*)\)" "") chi)))
         (defn contract-signatures [phi psi M] (if (or (original? phi) (original? psi)) #{(original-signature M)} #{}))
         (defn external-signatures-node [N M f]
           (union (let [H (N :H)]
                    (if (= (first (H :s)) :method-call)
                      (union (f (H :phi)) (f (H :psi)) #{(method-signature M H)})
                      (union (f (H :phi)) (f (H :psi)))))
                  (reduce union (for [[_ N2] (N :children)] (external-signatures-node N2 M f)))))
         (defn external-signatures [M] (external-signatures-node (M :T) M #(if (original? %) #{(original-signature M)} #{})))
         (defn external-method-signatures [M] (external-signatures-node (M :T) M (fn [_] #{})))

         ;;; Definition 3.9: Syntax of CSPLs
         (defn get-feature [PL F-M] (some #(if (starts-with? (-> F-M :S :name) (str % "_")) %) (PL :Fs)))
         (defn -get-method [PL S] (some #(if (= (erase-names S) (erase-names (% :S))) %) (PL :F-Ms)))
         (defn get-method-by-name [PL name] (some #(if (= name (-> % :S :name)) %) (PL :F-Ms)))
         (defn get-method-name [F-M] (join "_" (rest (split (-> F-M :S :name) #"_"))))
         (defn get-bare-method [F-M] (rename-method F-M (get-method-name F-M)))

         ;;; Definition 3.11: Semantics of CSPLs
         (defn get-bare-methods [PL F] (set (for [F-M (PL :F-Ms) :when (= (get-feature PL F-M) F)] (get-bare-method F-M))))
         (defn restrict [PL C n] (set (for [F C :when (some #(= (-> % :S :name) n) (get-bare-methods PL F))] F)))
         (defn direct-< [< C F1 F2] (and (contains? C F1) (contains? C F2) (< F1 F2) (not (some #(and (< F1 %) (< % F2)) C))))
         (defn last-feature [< C F] (and (contains? C F) (not (some #(< F %) C))))
         (defn derived-methods
           ([PL C i] (if (zero? i)
                       (set (for [F-M (PL :F-Ms)
                                  :when (last-feature (PL :<) (restrict PL C (get-method-name F-M)) (get-feature PL F-M))] F-M))
                       (set (for [F-M (derived-methods PL C (dec i)) F'-M' (PL :F-Ms)
                                  :let [F (get-feature PL F-M) F' (get-feature PL F'-M')]
                                  :when (and (contains? (external-method-signatures F-M) (original-signature F-M))
                                             (direct-< (PL :<) (restrict PL C (get-method-name F-M)) F' F)
                                             (= (get-method-name F'-M') (get-method-name F-M)))] F'-M'))))
           ([PL C] (reduce union (for [i (range) :let [F-Ms (derived-methods PL C i)] :while (seq F-Ms)] F-Ms))))
         (defn method-lookup [PL C]
           (into {} (for [F-M (PL :F-Ms) F'-M' (PL :F-Ms) S' (external-signatures F-M)
                          :let [F (get-feature PL F-M) F' (get-feature PL F'-M')
                                M-name (get-method-name F-M) M'-name (get-method-name F'-M')]
                          :when (or (and (= (S' :name) "original")
                                         (direct-< (PL :<) (restrict PL C M-name) F' F)
                                         (= M'-name M-name))
                                    (and (not= (S' :name) "original")
                                         (last-feature (PL :<) (restrict PL C (S' :name)) F')
                                         (= M'-name (S' :name))))] [S' F'-M'])))

         ;;;; Section 3.3: Proof Repositories
         ;;; Definition 3.12: Syntax of Programs
         (defn program [Cs Bs] {:Cs Cs :Bs Bs})
         (defn klass [name Fs Is] {:name name :Fs Fs :Is Is})
         (defn implementation [S requires ensures assignable body no-co-Ss co-Ss]
           {:S S :requires requires :ensures ensures :assignable assignable :body body :Ss (union no-co-Ss co-Ss) :co-Ss co-Ss})
         (defn implementations [P] (reduce union (map :Is (P :Cs))))
         (defn call [in to] {:in in :to to})
         (defn erase-names-call [c] (call (erase-names (c :in)) (erase-names (c :to))))
         (defn -binding [src dst] {:src src :dst dst})
         (defn remove-binding [P B] (program (P :Cs) (disj (P :Bs) B)))
         (defn remove-implementation [C I] (klass (C :name) (C :Fs) (disj (C :Is) I)))

         ;;; Definition 3.13: Direct and Extended Calls
         (defn direct-calls [i I] (let [Ss (if (zero? i) (I :Ss) (I :co-Ss))] (set (map #(call (erase-names (I :S)) %) Ss))))
         (defn extended-calls
           ([P i I Bs] (union (direct-calls i I)
                              (set (for [c (direct-calls i I)
                                         B Bs :when (= (erase-names-call (B :src)) (erase-names-call c))
                                         I' (implementations P) :when (= (erase-names (B :dst)) (erase-names (I' :S)))
                                         c' (extended-calls P (inc i) I' (disj Bs B))] c'))))
           ([P Bs] (reduce union (map #(extended-calls P 0 % Bs) (implementations P)))))

         ;;; Definition 3.14: Verification System
         (defn begin-proof [I] `(:begin-proof ~I))
         (defn continue-proof [D B] `(:continue-proof ~D ~B))

         ;;; Definition 3.15: Syntax of Proof Repository Domains
         (defn proof-descriptor [I Bs] {:I I :Bs Bs})
         (defn unbound-calls [P D] (difference (extended-calls P 0 (D :I) (D :Bs)) (set (map :src (D :Bs)))))
         (defn proof-descriptor-complete? [P D] (empty? (unbound-calls P D)))

         ;;; Definition 3.16: Semantics of Proof Repository Domains
         (defn add-binding [P B Ds]
           (let [delta-Ds (set (for [D Ds :when (contains? (unbound-calls P D) (B :src))]
                                 (proof-descriptor (D :I) (conj (D :Bs) B))))]
             (union Ds delta-Ds (reduce union (for [B' (set (for [D Ds B (D :Bs)] B))] (add-binding P B' delta-Ds))))))
         (defn proof-repository-domain [P]
           (let [I (first (implementations P)) B (first (P :Bs))]
             (cond B (add-binding P B (proof-repository-domain (remove-binding P B)))
                   I (conj (proof-repository-domain (program (for [C (P :Cs)] (remove-implementation C I)) (P :Bs)))
                           (proof-descriptor I #{}))
                   true #{})))

         ;;; Definition 3.17: Syntax and Semantics of Proof Repositories
         (defn proof-repository [Ds]
           (let [R (fn R [D Ds]
                     (if (empty? (D :Bs))
                       (begin-proof (D :I))
                       (let [[D' B] (first (for [D' Ds B (D :Bs)
                                                 :when (and (= (D' :I) (D :I)) (= (D' :Bs) (disj (D :Bs) B)))]
                                             [D' B]))]
                         (if D' (continue-proof D' B)))))]
             (for [D Ds :let [V (R D Ds)] :when V] [D V])))
         (defn sorted-proof-repository [Rs] (sort-by #(count (-> % first :Bs)) Rs))

         ;;; Definition 3.18: Semantics of Programs
         (defn complete-verification-states [P Rs] (map second (filter #(proof-descriptor-complete? P (first %)) Rs)))

         ;;;; Section 3.4: Reducing Method Semantics to Proof Repositories
         ;;; Definition 3.19: Supplementary Transformations
         (defn custom-signature [t n M] (signature t (-> M :S :name) n ()))
         (defn main-signature [M] (signature (-> M :S :type) (-> M :S :name) "main" (-> M :S :ps)))
         (defn translate-assignable [N] (let [ls (assignable-locations N)] (if (seq ls) (join ", " ls) "\\nothing")))
         (defn field-transformation [M]
           (set (conj (for [[t n] (union (M :Ls) (-> M :S :ps))] (signature t (-> M :S :name) n nil))
                      (signature (-> M :S :type) (-> M :S :name) "_result" nil))))
         (defn root-transformation [M b no-co-Ss]
           (let [phi (-> M :T :H :phi) psi (-> M :T :H :psi)]
             #{(implementation (main-signature M) phi psi (translate-assignable (M :T))
                               (str b "\nreturn _result;") no-co-Ss (contract-signatures phi psi M))}))
         (defn translate-parameters [ps names-only?] (join ", " (map (fn [[t n]] (if names-only? n (str t " " n))) ps)))
         (defn translate-statement [s]
           (cond (= (first s) :skip-statement) ";"
                 (= (first s) :assignment) (let [[_ _ ls es] s] (join "\n" (map #(str %1 " = " %2 ";") ls es)))
                 (= (first s) :method-call) (let [[_ _ [_ l-name] m as] s]
                                              (str l-name " = " m "(" (translate-parameters as true) ");"))))
         (defn inline-statement [N]
           (let [s (-> N :H :s) kind (first s)]
             (cond (= kind :abstract-statement) (inline-statement ((N :children) 1))
                   (= kind :composition)
                   (str (inline-statement ((N :children) 1)) (inline-statement ((N :children) 2)))
                   (= kind :selection)
                   (let [[_ _ chi-gs] s]
                     (str "if (!(" (xor-string chi-gs) "))\n"
                          "  throw new RuntimeException();\n"
                          (join "\n" (map-indexed #(str "if (" %2 ") {\n"
                                                        (inline-statement ((N :children) (inc %1)))
                                                        "}") chi-gs))
                          "\n"))
                   (= kind :repetition)
                   (let [[_ _ chi-i e-v chi-g] s]
                     (str "/*@ loop_invariant " chi-i ";\n"
                          "  @ decreases " e-v ";\n"
                          "  @ assignable " (translate-assignable N) ";\n"
                          "  @*/\n"
                          "while (" chi-g ") {\n"
                          (inline-statement ((N :children) 1))
                          "}\n"))
                   true (str (translate-statement s) "\n"))))

         ;;; Definition 3.20: Coarse-Grained Transformation
         (defn stub-class-transformation [l F-M]
           (set (for [[_ F'-M'] l :when (not= (-> F-M :S :name) (-> F'-M' :S :name))]
                  (assoc (klass (-> F'-M' :S :name) (field-transformation F'-M')
                                (root-transformation F'-M' "_();" #{(custom-signature "void" "_" F'-M')}))
                    :stub true))))
         (defn binding-transformation [l P]
           (set (for [{S :in S' :to} (extended-calls P #{}) :let [F'-M' (l S')] :when F'-M']
                  (-binding (call S S') (erase-names (main-signature F'-M'))))))
         (defn method-transformation [Is]
           (fn ([l i F-M] (if (zero? i)
                            (program (union #{(klass (-> F-M :S :name) (field-transformation F-M) (Is F-M))}
                                            (stub-class-transformation l F-M)) #{})
                            (let [P' ((method-transformation Is) l 0 F-M)]
                              (program (P' :Cs) (binding-transformation l P')))))
             ([l F-M] ((method-transformation Is) l 1 F-M))))
         (def coarse-grained-transformation
           (method-transformation
             (fn [F-M] (root-transformation F-M (if (method-complete? F-M)
                                                  (str (if *encode-locals?*
                                                         (str (join "\n" (for [[t n] (F-M :Ls)] (format "%s %s;" t n))) "\n")
                                                         "")
                                                       (inline-statement (F-M :T))) "_();")
                                            (external-method-signatures F-M)))))

         ;;; Definition 3.21: Fine-Grained Transformation
         (defn side-condition-transformations [F-M]
           (reduce union (for [N (nodes (F-M :T))
                               :let [phi (-> N :H :phi) psi (-> N :H :psi) s (-> N :H :s) kind (first s)]]
                           (cond (= kind :selection)
                                 (let [[_ _ chi-gs] s]
                                   #{(implementation (custom-signature "boolean" (str (N :label) "_sel") F-M)
                                                     phi "\\result" "\\nothing"
                                                     (str "return " (xor-string chi-gs) ";")
                                                     #{} (contract-signatures phi nil F-M))})
                                 (= kind :repetition)
                                 (let [[_ _ chi-i _ chi-g] s]
                                   #{(implementation (custom-signature "void" (str (N :label) "_init") F-M)
                                                     phi chi-i "\\nothing" ";" #{} (contract-signatures phi nil F-M))
                                     (implementation (custom-signature "boolean" (str (N :label) "_use") F-M)
                                                     chi-i (str "!\\result ==> (" psi ")") "\\nothing"
                                                     (str "return (" chi-g ");") #{} (contract-signatures nil psi F-M))})))))
         (def fine-grained-transformation
           (method-transformation (fn [F-M] (union (root-transformation F-M "_();" #{(custom-signature "void" "_" F-M)})
                                                   (set (for [N (nodes (F-M :T))
                                                              :let [phi (-> N :H :phi) psi (-> N :H :psi) s (-> N :H :s)]
                                                              :when (zero? (second s))]
                                                          (implementation (custom-signature "void" (str (N :label)) F-M)
                                                                          phi psi (translate-assignable N)
                                                                          (translate-statement s)
                                                                          (external-signatures-node N F-M (fn [_] #{}))
                                                                          (contract-signatures phi psi F-M))))
                                                   (side-condition-transformations F-M)))))

         ;;;; Section 3.5: Reducing CSPL Semantics to Proof Repositories
         ;;; Definition 3.22: Union of Programs
         (defn program-union [P1 P2]
           (program (let [Cs (union (P1 :Cs) (P2 :Cs))]
                      (set (for [C Cs :when (not (and (C :stub) (some #(and (= (C :name) (% :name)) (not (% :stub))) Cs)))] C)))
                    (union (P1 :Bs) (P2 :Bs))))

         ;;; Definition 3.23: CSPL Transformation
         (defn cspl-transformation [PL t]
           (reduce program-union (program #{} #{}) (for [C (PL :Cs) F-M (derived-methods PL C)] (t (method-lookup PL C) F-M))))

         ;;; Definition 3.24: Inverse Binding Transformation
         (defn inverse-binding-transformation [PL Bs]
           (into {} (for [{{_ :in to :to} :src dst :dst} Bs]
                      [to (-get-method PL (signature (dst :type) nil (dst :C-name) (dst :ps)))])))
         (defn method-lookup-contains? [PL C Bs]
           (subset? (set (inverse-binding-transformation PL Bs)) (set (method-lookup PL C))))

         ;;; Definition 3.25: Pruned Proof Repository
         (defn pruned-proof-repository-domain [PL Ds]
           (set (for [D Ds :when (and (not (starts-with? (-> D :I :body) "_();"))
                                      (some #(and (contains? (derived-methods PL %) (get-method-by-name PL (-> D :I :S :C-name)))
                                                  (method-lookup-contains? PL % (D :Bs))) (PL :Cs)))] D)))
         (defn pruned-proof-repository [PL P]
           (let [Ds (pruned-proof-repository-domain PL (proof-repository-domain P))] [Ds (proof-repository Ds)]))

         ;;;; Section 3.6: Discussion
         ;;; Late Splitting
         (defn late-splitting-proof-repository-domain
           ([Ds I P]
            (let [->paths (fn f [Ds D]
                            (if (seq (D :Bs))
                              (reduce union (for [B (D :Bs) :let [D' (update D :Bs #(disj % B))]]
                                              (if (Ds D') (set (for [path (f Ds D')] (conj path B))) #{})))
                              #{[]}))
                  path-> (fn f [D path]
                           (conj (let [B (first path) D' (update D :Bs #(conj % B))] (if B (f D' (rest path)) #{})) D))
                  cartesian (fn f [xs] (if (empty? xs) '(()) (for [more (f (rest xs)) x (first xs)] (cons x more))))
                  common-prefix (fn f [p p'] (if (= (first p) (first p')) (inc (f (rest p) (rest p'))) 0))
                  score (fn [paths] (reduce + (for [p paths p' paths :when (not= p p')] (common-prefix p p'))))
                  optimal-paths (fn [path-family] (last (sort-by score (cartesian path-family))))
                  complete-Ds (filter #(and (= (% :I) I) (proof-descriptor-complete? P %)) Ds)
                  path-family (map #(->paths Ds %) complete-Ds)]
              (reduce union (for [[D path] (map vector (map #(assoc % :Bs #{}) complete-Ds) (optimal-paths path-family))]
                              (path-> D path)))))
           ([Ds P] (reduce union (for [I (implementations P)] (late-splitting-proof-repository-domain Ds I P)))))

         ;;;; Core Algorithm
         (defn main [PL t query-strategy]
           (assert (cspl? PL))
           (let [P (cspl-transformation PL t)]
             (assert (program? P))
             (let [[Ds Rs] (pruned-proof-repository PL P)
                   Rs (sorted-proof-repository Rs)
                   Rs (cond
                        (= query-strategy :complete) (filter (fn [[D _]] (proof-descriptor-complete? P D)) Rs)
                        (= query-strategy :late-splitting)
                        (let [Ds' (late-splitting-proof-repository-domain Ds P)] (filter (fn [[D _]] (Ds' D)) Rs))
                        true Rs)]
               (assert (proof-repository? Rs P))
               [P Rs])))

         ;;;; Debugging
         (defn dump-binding [B] (str (-> B :src :in :C-name) "::" (-> B :src :in :name) "."
                                     (-> B :src :to :name) " -> " (-> B :dst :C-name)))
         (defn dump-program [P]
           (list (for [C (P :Cs)]
                   (list (C :name)
                         (map #(str (% :type) " " (% :name)) (C :Fs))
                         (map #(assoc (dissoc (dissoc % :Ss) :co-Ss)
                                 :S (str (-> % :S :type) " " (-> % :S :name) "("
                                         (translate-parameters (-> % :S :ps) false) ")")) (C :Is))))
                 (map dump-binding (P :Bs))))
         (defn dump-proof-descriptor [D]
           (list (str (-> D :I :S :C-name) "::" (-> D :I :S :name)) (map dump-binding (D :Bs))))
         (defn dump-verification-state [V]
           (cond (= (first V) :begin-proof)
                 (list :begin-proof (str (-> V second :S :C-name) "::" (-> V second :S :name)))
                 (= (first V) :continue-proof)
                 (list :continue-proof (-> V second dump-proof-descriptor) (-> V (nth 2) dump-binding))))
         (defn dump-proof-repository-domain [Ds] (map dump-proof-descriptor Ds))
         (defn dump-proof-repository [Rs] (map (fn [[D V]] (list (dump-proof-descriptor D) (dump-verification-state V))) Rs))
         (defn dump-verification-states [Vs] (map dump-verification-state Vs))

         ;;;; Java Interop
         (defn ->Setting [key value] (Program$Setting. (if (keyword? key) (name key) (str key))
                                                       (if (keyword? value) (name value) (str value))))
         (defn ->Macro [find replace] (Macro. find replace true))
         (defn ->Signature [S]
           (if (nil? (S :ps))
             (Signature$Field. (S :type) (S :C-name) (S :name))
             (Signature$Method. (S :type) (S :C-name) (S :name) (map #(Utils$Pair. (first %) (second %)) (S :ps)))))
         (defn Signature-> [s] (signature (.type s) (if (not-empty (.className s)) (.className s))
                                          (.name s) (map #(list (.first %) (.second %)) (.parameters s))))
         (defn ->CallSignature [call] (Signature$Call. (->Signature (call :in)) (->Signature (call :to))))
         (defn ->ExtendedCallSignatures [P i I Bs] (map ->CallSignature (extended-calls P i I Bs)))
         (defn ->Field [F] (Program$Field. (->Signature F)))
         (defn ->Call [S] (Program$Call. (->Signature S)))
         (defn ->Implementation [I]
           (Program$Implementation. I (->Signature (I :S))
                                    (I :body) (I :requires) (I :ensures) (I :assignable)
                                    (for [S (I :Ss)] (->Call S))))
         (defn ->Klass [C] (Program$Klass. (C :name) (for [F (C :Fs)] (->Field F)) (for [I (C :Is)] (->Implementation I))))
         (defn ->Binding [B] (Program$Binding. B (->CallSignature (B :src)) (->Signature (B :dst))))
         (defn ->Program [P settings macros]
           (Program. P settings macros (for [C (P :Cs)] (->Klass C)) (for [B (P :Bs)] (->Binding B))))
         (defn ->ProofDescriptor [program D]
           (Program$ProofDescriptor. program D (->Signature (-> D :I :S))
                                     (for [B (D :Bs)] (Utils$Pair. (->CallSignature (B :src)) (->Signature (B :dst))))))
         (defn ->VerificationState [program V]
           (cond (= (first V) :begin-proof)
                 (Program$BeginProof. program (->Signature (-> V second :S)))
                 (= (first V) :continue-proof)
                 (Program$ContinueProof. program (->ProofDescriptor program (second V))
                                         (->CallSignature (-> V (nth 2) :src))
                                         (->Signature (-> V (nth 2) :dst)))))
         (defn ->ProofRepository [program Rs]
           (Program$ProofRepository. program (for [[D V] Rs] (Utils$Pair. (->ProofDescriptor program D)
                                                                          (->VerificationState program V)))))
         (defn ->Main [PL t query-strategy]
           (let [[P Rs] (main PL t query-strategy)]
             (->ProofRepository (->Program P (PL :settings) (PL :macros)) Rs)))
         (defn ->VerificationSystem [proof-repository abstract-contracts? f]
           (with-open [verification-system
                       (VerificationSystem. proof-repository (CodeGenerator. (.program proof-repository) abstract-contracts?)
                                            abstract-contracts?)]
             (f verification-system)))

         ;;;; Evaluation
         (defn signature->csv [S] (str (S :C-name) "_" (S :name)))
         (defn binding->csv [B]
           (str (signature->csv (-> B :src :in)) "_" (signature->csv (-> B :src :to)) "_" (signature->csv (-> B :dst))))
         (defn proof-descriptor->csv [D]
           (str (-> D :I :S :C-name) "_" (-> D :I :S :name) "_" (join "_" (sort (map binding->csv (D :Bs))))))

         ;;;; DSL
         (defn forall
           ([f g] (let [s (gensym)] (format (str "(\\forall int %1$s; " (f s) "; " (g s) ")") s)))
           ([f f' g] (forall f (fn [x] (forall (f' x) (fn [y] (g x y)))))))
         (defn exists
           ([f g] (let [s (gensym)] (format (str "(\\exists int %1$s; " (f s) "; " (g s) ")") s)))
           ([f f' g] (exists f (fn [x] (exists f' (fn [y] (g x y)))))))
         (defn in
           ([i < <' j] (fn [x] (if (and (= < :<=) (= <' :<=))
                                 (format "%s <= %s && %s %s %s" i x x (name <') j)
                                 (format "%s %s %s %s %s" i (name <) x (name <') j))))
           ([A] (in 0 :<= :< (str A ".length"))))
         (defn => [s & children]
           (node nil s nil (reduce (fn [acc [k v]] (if v (assoc acc k v) acc)) {} (map-indexed #(list (inc %1) %2) children))))
         (defn -=> [s & children] nil)
         (defn phi [N i]
           (let [kind (-> N :H :s first) phi (-> N :H :phi)]
             (cond (= kind :abstract-statement) phi
                   (= kind :composition) (let [[_ _ chi-m] (-> N :H :s)] (if (= i 1) phi chi-m))
                   (= kind :selection) (let [[_ _ chi-gs] (-> N :H :s)] (str "(" phi ") && (" (chi-gs (dec i)) ")"))
                   (= kind :repetition) (let [[_ _ chi-i _ chi-g] (-> N :H :s)] (str "(" chi-i ") && (" chi-g ")")))))
         (defn psi [N i]
           (let [kind (-> N :H :s first) psi (-> N :H :psi)]
             (cond (= kind :abstract-statement) psi
                   (= kind :composition) (let [[_ _ chi-m] (-> N :H :s)] (if (= i 1) chi-m psi))
                   (= kind :selection) psi
                   (= kind :repetition) (let [[_ _ chi-i e-v _] (-> N :H :s)]
                                          (str "(" chi-i ") && 0 <= (" e-v ") && (" e-v ") < \\old(" e-v ")")))))
         (defn propagate [N]
           (update N :children #(into {} (for [[i N'] %] [i (propagate (-> N' (assoc-in [:H :phi] (phi N i))
                                                                           (assoc-in [:H :psi] (psi N i))))]))))
         (defn T [phi psi N] (propagate (-> N (assoc-in [:H :phi] phi) (assoc-in [:H :psi] psi))))
         (defn S [spec] (Signature-> (Signature$Method. spec)))
         (defn M [spec _ Ls T] {:S (S spec) :Ls (set Ls) :T T})
         (defn -M [spec _ Ls T] nil)
         (defn CSPL [order Cs settings macros F-Ms]
           {:Fs       (set order)
            :Cs       (set (map set Cs))
            :<        (fn [a b] (< (.indexOf order a) (.indexOf order b)))
            :settings (for [[key value] settings] (->Setting key value))
            :macros   (for [[find replace] macros] (->Macro find replace))
            :F-Ms     (set (filter identity F-Ms))})

         ;;;; Imperative Shell
         (defn log-level! [log-level]
           (assert (#{:trace :debug :info :warning :error :off} log-level))
           (.activate (.level (Configurator/currentConfig) (Level/valueOf (s/upper-case (name log-level))))))
         (defn key! ([^String file] (KeYBridge/runKey (if file (File. file)))) ([] (key! nil)))
         (defn load! [file]
           (if (some #(ends-with? (lower-case file) %) #{".key" ".proof" ".java"}) (key! file) (load-file file)))
         (defn check!
           ([PL t query-strategy]
            (let [Ds (union (proof-repository-domain (cspl-transformation PL fine-grained-transformation))
                            (proof-repository-domain (cspl-transformation PL coarse-grained-transformation)))
                  D-csvs (dedupe (sort (map proof-descriptor->csv Ds)))]
              (if (= query-strategy :product-based)
                (let [start (Instant/now)
                      PLs (for [C (PL :Cs)] (assoc PL :Cs #{C}))
                      results (for [PL PLs] (check! PL t :complete))]
                  [(join "; " D-csvs)
                   (Evaluation/reduce D-csvs (map second results))
                   (.toMillis (Duration/between start (Instant/now)))])
                (let [start (Instant/now)
                      proof-repository (->Main PL t query-strategy)]
                  (log-level! (keyword (.getSettingValue (.program proof-repository) "log-level")))
                  (Logger/info (str "\n" (.dump (.program proof-repository))))
                  (->VerificationSystem
                    proof-repository (contains? #{:exhaustive :late-splitting} query-strategy)
                    (fn [verification-system]
                      (.verify verification-system)
                      (let [check (.check verification-system)]
                        (Logger/info (str "\n" (.dump verification-system)))
                        (Logger/info (str "\n" (.sumStatistics verification-system)))
                        (if check
                          (Logger/info (str "Program is CORRECT"))
                          (do (Logger/error (str "Program is INCORRECT"))
                              (Logger/error (str "Incorrect proofs:\n"
                                                 (.dumpIncorrectProofs verification-system)))))
                        [(join "; " D-csvs)
                         (Evaluation. D-csvs (.proofs verification-system))
                         (.toMillis (Duration/between start (Instant/now)))])))))))
           ([PL t] (check! PL t :exhaustive)))
         (defn evaluate!
           ([directory PL t query-strategy optimization-strategy encode-locals?]
            (assert (contains? #{coarse-grained-transformation fine-grained-transformation} t))
            (assert (contains? #{:exhaustive :late-splitting :complete :product-based} query-strategy))
            (assert (contains? #{nil :none :default :strict} optimization-strategy))
            (assert (contains? #{nil false true} encode-locals?))
            (let [abstract-contracts? (contains? #{:exhaustive :late-splitting} query-strategy)
                  store (format "%s-%s%s%s" (if (= t coarse-grained-transformation) "coarse" "fine")
                                (name query-strategy)
                                (if optimization-strategy (str "-" (name optimization-strategy)) "")
                                (if encode-locals? "-local" ""))
                  PL (update PL :settings #(concat (conj % (->Setting :store-proof-contexts (str directory "/" store)))
                                                   (if optimization-strategy
                                                     [(->Setting :optimization-strategy optimization-strategy)] [])))]
              (when (and (= (not (nil? optimization-strategy)) abstract-contracts?)
                         (= (not (nil? encode-locals?)) (= t coarse-grained-transformation)))
                (Utils/deleteDirectoryIfExists (str directory "/" store))
                [store (binding [*encode-locals?* encode-locals?] (check! PL t query-strategy))])))
           ([directory PL]
            (let [results
                  (for [t #{coarse-grained-transformation fine-grained-transformation}
                        query-strategy #{:exhaustive :late-splitting :complete :product-based}
                        optimization-strategy #{nil :none :default :strict}
                        encode-locals? #{nil false true}]
                    (let [[store [heading evaluation total-time]]
                          (evaluate! directory PL t query-strategy optimization-strategy encode-locals?)]
                      (if store
                        (let [row #(str store "; " %)
                              semantics (.evaluateSemanticsCsv evaluation) nodes (.evaluateNodesCsv evaluation)
                              time (.evaluateTimeCsv evaluation) avg-time (.evaluateAvgTimeCsv evaluation)]
                          [(str "; " heading) (row semantics) (row nodes) (row time) (row avg-time) (row total-time)]))))
                  results (filter identity results)
                  save #(Utils/writeFile (str directory "/" %1 ".csv") (reduce %2 (first (first results)) results))]
              (save "semantics" (fn [acc [_ semantics _ _ _ _]] (str acc "\n" semantics)))
              (save "nodes" (fn [acc [_ _ nodes _ _ _]] (str acc "\n" nodes)))
              (save "time" (fn [acc [_ _ _ time _ _]] (str acc "\n" time)))
              (save "avgTime" (fn [acc [_ _ _ _ avg-time _]] (str acc "\n" avg-time)))
              (Utils/writeFile (str directory "/totalTime.csv")
                               (reduce (fn [acc [_ _ _ _ _ total-time]] (str acc "\n" total-time)) "" results))))))