;; We're trying to bound the number of rows in a query answer
;; The query might be the derivative of an actual query,
;; for which we want to find the sensitivity

;; Let us have two tables, R1(a1,a2) and R2(b1,b2)
;; Let b1 be unique in R2
;; We have the query
;; SELECT * FROM R1 INNER JOIN R2 on a2 = b1 WHERE b2 > 10
;; We want to find its derivative wrt. R1.
;; Let (x1,x2) be a fixed row that is not in R1.
;; The derivative "query" is
;; SELECT (x1,x2,b1,b2) FROM R2 WHERE b1 = x2 && b2 > 10
(declare-const x1 Int)
(declare-const x2 Int)

(declare-const y11 Int) ;; First possible row from R2 starts here
(declare-const y12 Int) ;; ... and ends here.
(declare-const y21 Int) ;; Second possible row from R2 starts here
(declare-const y22 Int) ;; ... and ends here.

(assert (=> (= y11 y12) (= y21 y22))) ;; uniqueness assertion. Try commenting it out
(assert (= x2 y11)) ;; the join clause, first possible row
(assert (= x2 y12)) ;; the join clause, second possible row

(assert (> y21 10)) ;; where-clause, first possible row
(assert (> y22 10)) ;; where-clause, first possible row

(declare-fun f (Int Int Int Int) Int) ;; "identity" of a row in the output

(assert (distinct (f x1 x2 y11 y21) (f x1 x2 y12 y22)))

(check-sat)
;; (get-model) ;; no model, if uniqueness is asserted
