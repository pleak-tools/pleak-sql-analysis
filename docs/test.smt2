;;; generic database stuff

(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))
(declare-datatypes (T) ((Maybe none (some (elem T)))))
(define-fun bounded ((l Int) (x Int) (u Int)) Bool
  (and (<= l x) (< x u)))

;;; some tables
(declare-const t1 (Array Int (Maybe Int)))
(declare-const t1-size Int)

(declare-const t2 (Array Int (Maybe Int)))
(declare-const t2-size Int)

;;; non-null constraint on t1
(assert (forall ((i Int))
    (=> (bounded 0 i t1-size) (is-some (select t1 i)))
))

;;; unique constraint on t1
(assert (forall ((i Int) (j Int))
    (=> (and (<= 0 i) (<= 0 j) (< i t1-size) (< j t1-size))
        (distinct (select t1 i) (select t1 j))
    )
))

;;; insert extra row into t2
(declare-const t3 (Array Int (Maybe Int)))
(declare-const t3-size Int)
(declare-const row (Maybe Int))

(assert (= t3-size (+ 1 t2-size)))
(assert (= t3 (store t2 t2-size row)))

; check that it's able to tell that first elements are equal
(push)
 (assert (= t2-size 2))
 (assert (= (select t2 0) (select t3 0)))
 ; (assert (distinct (select t2 1) (select t3 1)))
 (echo "sanity check")
 (check-sat)
(pop)

; difference tables (no need for sizes yet)
(declare-const t1t3 (Array Int Int (Maybe (Pair Int Int))))
(declare-const t1t2 (Array Int Int (Maybe (Pair Int Int))))

(echo "Define first query result.")
(assert (forall ((i Int) (j Int))
    (=> (and (bounded 0 i t1-size) (bounded 0 j t2-size))
    (let ((t1-val (select t1 i)) (t2-val (select t2 j)))
        (= (select t1t2 i j)
           (ite (and (is-some t1-val) (is-some t2-val) (= t1-val t2-val))
                (some (mk-pair (elem t1-val) (elem t2-val)))
                (as none (Maybe (Pair Int Int)))))
    ))
))

(check-sat)

(echo "Define second query result.")
(assert (forall ((i Int) (j Int))
    (=> (and (bounded 0 i t1-size) (bounded 0 j t3-size))
    (let ((t1-val (select t1 i)) (t3-val (select t3 j)))
        (= (select t1t3 i j)
           (ite (and (is-some t1-val) (is-some t3-val) (= t1-val t3-val))
                (some (mk-pair (elem t1-val) (elem t3-val)))
                (as none (Maybe (Pair Int Int)))))
    ))
))

(check-sat)

(echo "Define difference table.")
(declare-const diff (Array Int Int (Maybe (Pair Int Int))))

;;; diff = t1t3 - t1t2
(assert (forall ((i Int) (j Int))
    (=> (and (bounded 0 i t1-size) (bounded 0 j t3-size))
    (let ((val (select t1t3 i j)))
        (=  (select diff i j)
            (ite (and (is-some val)
                      (not (and (bounded 0 i t1-size) (bounded 0 j t2-size) (is-some (select t1t2 i j))))
                 )
                 val
                 (as none (Maybe (Pair Int Int)))
            )
        )
    ))
))

(declare-const flat (Array Int Int))
(assert (forall ((i Int) (j Int))
    (=> (and (bounded 0 i t1-size) (bounded 0 j t3-size))
        (= (select flat (+ (* i t3-size) j))
           (ite (is-some (select diff i j)) 1 0)
        )
    )
))

(declare-const prefix-sum (Array Int Int))
(assert (= (select prefix-sum 0) (select flat 0)))
(assert (forall ((i Int))
    (=> (bounded 1 i (* t1-size t3-size))
        (= (select prefix-sum i)
           (+ (select prefix-sum (- i 1)) (select flat i))
        )
    )
))


(check-sat)

(push)
 (echo "Difference table playground:")
 ; 2 x 3
 (assert (> t1-size 0))
 (assert (> t2-size 0))

 (assert (= t1-size 2))
 (assert (= t2-size 2))
 ; (assert (= t3-size 3))
 ; (check-sat)

 ; check that common part is different
 ; (assert (is-some (select diff 0 2)))
 ; (assert (is-some (select diff 1 2)))
 (assert (= (select prefix-sum (- (* t1-size t3-size) 1)) 2))
 (check-sat)
 ; (get-model)
(pop)
