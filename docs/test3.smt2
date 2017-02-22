;; We're trying to bound the number of rows in a query answer
;; The query might be the derivative of an actual query,
;; for which we want to find the sensitivity

;; Let us have two tables, R1(a0,a1,a2) and R2(b0,b1,b2)
;; Let a0 be unique in R1
;; Let b0 be unique in R2
;; Let b1 be unique in R2
;; We have the query
;; SELECT * FROM R1 INNER JOIN R2 on a2 = b1 WHERE b2 > 10
;; We want to find its derivative wrt. R1.
;; Let (x1,x2) be a fixed row that is not in R1.


;; Derivative of following query over R1:
;; SELECT * FROM R1 INNER JOIN R2 on a2 = b1 WHERE b2 > 10
;; SELECT (x0,x1,x2,b0,b1,b2) FROM R2 WHERE b1 = x2 && b2 > 10
(push)
  (declare-const x0 Int)
  (declare-const x1 Int)
  (declare-const x2 Int)

  (declare-const y01 Int)
  (declare-const y02 Int)

  (declare-const y11 Int) ;; First possible row from R2 starts here
  (declare-const y12 Int) ;; ... and ends here.

  (declare-const y21 Int) ;; Second possible row from R2 starts here
  (declare-const y22 Int) ;; ... and ends here.

  ;; uniqueness assertion. Try commenting it out
  (assert (=> (= y01 y02) (and (= y11 y12) (= y21 y22))))
  (assert (=> (= y11 y12) (and (= y01 y02) (= y21 y22))))

  ;; b1 = x2
  (assert (= y11 x2)) ;; the join clause, first possible row
  (assert (= y12 x2)) ;; the join clause, second possible row

  ;; b2 > 10
  (assert (> y21 10)) ;; where-clause, first possible row
  (assert (> y22 10)) ;; where-clause, first possible row

  (declare-fun f (Int Int Int Int Int Int) Int) ;; "identity" of a row in the output

  (assert (
      distinct
          (f x0 x1 x2 y01 y11 y21)
          (f x0 x1 x2 y02 y12 y22)
  ))

  (echo "unsat?")
  (check-sat)
(pop)

;; SELECT 1 FROM R1, R2
;; => SELECT a0, b0, 1 FROM R1, R2
;; looking at: COUNT(SELECT a0, b0, 1 FROM R2)
(push)
  (declare-const x0 Int)
  (declare-const x1 Int)
  (declare-const x2 Int)

  (declare-const y01 Int)
  (declare-const y02 Int)

  (declare-const y11 Int) ;; First possible row from R2 starts here
  (declare-const y12 Int) ;; ... and ends here.

  (declare-const y21 Int) ;; Second possible row from R2 starts here
  (declare-const y22 Int) ;; ... and ends here.

    ;; uniqueness assertion. Try commenting it out
  (assert (=> (= y01 y02) (and (= y11 y12) (= y21 y22))))

  (declare-fun f (Int Int Int Int Int Int) Int) ;; "identity" of a row in the output

  (assert (
      distinct
          (f x0 x1 x2 y01 y11 y21)
          (f x0 x1 x2 y02 y12 y22)
  ))

  (echo "sat?")
  (check-sat)
(pop)