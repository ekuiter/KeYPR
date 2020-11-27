(def PL
  (CSPL
    ["List" "Ordered" "Set"]
    [["List"] ["List" "Ordered"] ["List" "Set"] ["List" "Ordered" "Set"]]
    [[:strategy-property "NON_LIN_ARITH_OPTIONS_KEY = NON_LIN_ARITH_DEF_OPS"] [:dry-run? false]]
    [["in[($A, $i)" ((in 0 :<= :< "$A.length") "$i")]
     ["in]($A, $i)" ((in 0 :<= :<= "$A.length") "$i")]
     ["appAllIn($A', $i, $j, $A)" (forall (in "$i" :<= :< "$j") #(format "appIn($A', $A[%s], $i, $j)" %))]
     ["appAll($A', $A)" (forall (in "$A") #(format "app($A', $A[%s])" %))]
     ["app($A, $x)" "appIn($A, $x, 0, $A.length)"]
     ["appIn($A, $x, $i, $j)" (exists (in "$i" :<= :< "$j") #(format "$A[%s] == $x" %))]
     ["isSorted($A)" (forall (in "$A") #(in % :< :< "$A.length") (fn [x y] (format "$A[%s] <= $A[%s]" x y)))]
     ["isSet($A)" (forall (in "$A") (constantly (in "$A"))
                          (fn [x y] (format "%s != %s ==> $A[%s] != $A[%s]" x y x y)))]]

    [(M "int[] ::List_Insert(int[] A, int x)"
        "Inserts an integer into a list. Uses the corrected CbC tree from the thesis."
        [["int" "i"]]
        (T "A.length > 0" "app(_result, x) && appAll(_result, A)"
           (let [inv (str "_result.length == A.length + 1 && _result[_result.length - 1] == x && "
                          "in](A, i) && appAllIn(_result, 0, i, A)")]
                (=> (abstract-statement)
                    (=> (composition (str inv " && i == 0"))
                        (=> (assignment ["i" "_result" "_result[_result.length - 1]"]
                                        ["0" "new int[A.length + 1]" "x"]))
                        (=> (repetition inv "A.length - i" "i < A.length")
                            (=> (assignment ["_result[i]" "i"] ["A[i]" "i + 1"]))))))))

     (M "boolean ::List_Search(int[] A, int x)"
        "Performs a linear search on a list. Based on Kourie and Watson, p. 56ff.
         Modified to allow for the absence of the searched element."
        [["int" "i"]]
        (T "A.length > 0" "_result == true <==> app(A, x)"
           (let [inv "-1 <= i < A.length && !appIn(A, x, i + 1, A.length)"]
                (=> (abstract-statement)
                    (=> (composition inv)
                        (=> (assignment ["i"] ["A.length - 1"]))
                        (=> (composition "i != -1 <==> app(A, x)")
                            (=> (repetition inv "i + 1" "i >= 0 && A[i] != x")
                                (=> (assignment ["i"] ["i - 1"])))
                            (=> (selection ["i == -1" "i != -1"])
                                (=> (assignment ["_result"] ["false"]))
                                (=> (assignment ["_result"] ["true"])))))))))

     (M "int[] ::Ordered_Insert(int[] A, int x)"
        "Inserts an integer into an ordered list."
        []
        (T "original_pre(A, x) && isSorted(A)" "original_post(A, x) && isSorted(_result)"
           (=> (abstract-statement)
               (=> (composition "original_post(A, x)")
                   (=> (method-call ["int[]" "_result"] "original" [["int[]" "A"] ["int" "x"]]))
                   (=> (method-call ["int[]" "_result"] "Sort" [["int[]" "_result"]]))))))

     (M "boolean ::Ordered_Search(int[] A, int x)"
        "Performs a binary search on a list. Based on Kourie and Watson, p.66ff.
         Requires NON_LIN_ARITH_DEF_OPS."
        [["int" "oldL"] ["int" "l"] ["int" "h"]]
        (let [inv "isSorted(A) && (app(A, x) ==> appIn(A, x, l, h)) && in](A, h) && in](A, l)"]
             (T "original_pre(A, x) && isSorted(A)" "original_post(A, x)"
                (=> (abstract-statement)
                    (=> (composition (str inv " && h <= l + 1"))
                        (=> (composition inv)
                            (=> (assignment ["l" "h"] ["0" "A.length"]))
                            (=> (repetition inv "h - l" "h > l + 1")
                                (=> (selection ["x < A[(l+h)/2]" "x == A[(l+h)/2]" "x > A[(l+h)/2]"])
                                    (=> (assignment ["h"] ["(l+h)/2"]))
                                    (=> (assignment ["oldL" "l" "h"] ["l" "(l+h)/2" "(oldL+h)/2+1"]))
                                    (=> (assignment ["l"] ["(l+h)/2"])))))
                        (=> (selection ["h == l + 1" "h < l + 1"])
                            (=> (selection ["A[l] == x" "A[l] != x"])
                                (=> (assignment ["_result"] ["true"]))
                                (=> (assignment ["_result"] ["false"])))
                            (=> (assignment ["_result"] ["false"]))))))))

     (M "int ::Ordered_Min(int[] A, int start)"
        "Searches for the minimum element in A, starting at start.
         Based on Ahrendt, Beckert et al., p. 559."
        [["int" "cnt"]]
        (T "A.length > 0 && in[(A, start)"
           (str "start <= _result && _result < A.length &&"
                (forall (in "start" :<= :< "A.length") #(format "A[_result] <= A[%s]" %)))
           (let [inv (str "in[(A, start) && start <= cnt && cnt <= A.length && "
                          "start <= _result && _result < A.length && start < A.length && "
                          (forall (in "start" :<= :< "cnt") #(format "A[_result] <= A[%s]" %)))]
                (=> (abstract-statement)
                    (=> (composition "in[(A, start) && cnt == start && _result == start")
                        (=> (assignment ["cnt" "_result"] ["start" "start"]))
                        (=> (repetition inv "A.length - cnt" "cnt < A.length")
                            (=> (composition (str inv " && cnt < A.length && A[cnt] >= A[_result]"))
                                (=> (selection ["A[cnt] < A[_result]" "A[cnt] >= A[_result]"])
                                    (=> (assignment ["_result"] ["cnt"]))
                                    (=> (skip-statement)))
                                (=> (assignment ["cnt"] ["cnt + 1"])))))))))

     (M "int[] ::Ordered_SortImpl(int[] A)"
        "Performs selection sort on a list. Based on Ahrendt, Beckert et al., p. 559."
        [["int" "i"] ["int" "pos"] ["int" "cnt"] ["int" "tmp"]]
        (T "A.length > 0"
           (forall (in 0 :<= :< "_result.length - 1") #(format "_result[%s] <= _result[%s + 1]" % %))
           (let [inv (str "A.length > 0 && _result.length == A.length && in[(_result, pos) && in[(_result, i) && "
                          (forall (in 0 :<= :< "pos - 1") #(format "_result[%s] <= _result[%s + 1]" % %))
                          " && (pos > 0 ==> " (forall (in "pos" :<= :< "_result.length")
                                                      #(format "_result[pos - 1] <= _result[%s]" %)) ")")]
                (=> (abstract-statement)
                    (=> (composition (str "A.length > 0 && _result.length == A.length && "
                                          "appAll(A, _result) && appAll(_result, A)"))
                        (=> (composition "A.length > 0 && _result.length == A.length && i == 0")
                            (=> (assignment ["_result" "i"] ["new int[A.length]" "0"]))
                            (=> (repetition (str "A.length > 0 && _result.length == A.length && in](A, i) && "
                                                 "appAllIn(_result, 0, i, A) && appAllIn(A, 0, i, _result)")
                                            "A.length - i" "i < A.length")
                                (=> (assignment ["_result[i]" "i"] ["A[i]" "i + 1"]))))
                        (=> (composition "A.length > 0 && _result.length == A.length && pos == 0 && i == 0")
                            (=> (assignment ["pos" "i"] ["0" "0"]))
                            (=> (repetition inv "_result.length - pos" "pos < _result.length - 1")
                                (=> (composition (str inv " && pos < _result.length - 1 && "
                                                      (forall (in "pos" :<= :< "_result.length")
                                                              #(format "_result[i] <= _result[%s]" %))
                                                      " && pos <= i && i < _result.length"))
                                    (=> (method-call ["int" "i"] "Min" [["int[]" "_result"] ["int" "pos"]]))
                                    (=> (assignment ["tmp" "_result[i]" "_result[pos]" "pos"]
                                                    ["_result[i]" "_result[pos]" "tmp" "pos+1"]))))))))))

     (M "int[] ::Ordered_Sort(int[] A)"
        "Stub for a sorting algorithm as required by Ordered_Insert."
        [["int" "i"] ["int" "pos"] ["int" "cnt"] ["int" "tmp"]]
        (T "A.length > 0" "appAll(A, _result) && appAll(_result, A) && isSorted(_result)"
           (=> (abstract-statement))))

     (M "int[] ::Set_Uniq(int[] A)"
        "Stub for an algorithm that removes duplicates as required by Set_Insert."
        []
        (T "A.length > 0" "appAll(A, _result) && appAll(_result, A) && isSet(_result)"
           (=> (abstract-statement))))

     (M "int[] ::Set_Insert(int[] A, int x)"
        "Inserts an integer into an (ordered or unordered) set."
        [["boolean" "found"]]
        (T "original_pre(A, x) && isSet(A)"
           "(app(A, x) ==> _result == A) && (!app(A, x) ==> true) && isSet(_result)"
           (=> (abstract-statement)
               (=> (composition "original_pre(A, x) && isSet(A) && (found == true <==> app(A, x))")
                   (=> (method-call ["boolean" "found"] "Search" [["int[]" "A"] ["int" "x"]]))
                   (=> (selection ["found == true" "found == false"])
                       (=> (assignment ["_result"] ["A"]))
                       (=> (composition "A.length > 0 && original_post(A, x) && !app(A, x)")
                           (=> (method-call ["int[]" "_result"] "original" [["int[]" "A"] ["int" "x"]]))
                           (=> (method-call ["int[]" "_result"] "Uniq" [["int[]" "A"]]))))))))]))

(evaluate! "results" PL)