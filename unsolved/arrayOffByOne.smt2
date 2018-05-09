;; CHC for the equivalence of the following two programs:

;; const int *a
;; const int n
;; precondition: n > 0
;; postcondition result1 == result2

;; f1() {
;;   for i = 0 .. n
;;     a[i] := a[i] + 1
;;   s = 0
;;   for i = 0 .. n
;;     s := s + a[i] + 1
;;   return s
;; }

;; f2() {
;;   for i = 0 .. n
;;     a[i] := a[i] + 2
;;   int s := 0
;;   for i = 0 .. n
;;     s := s + a[i]
;;   return s
;; }

;; Coupling invariants for the loops are INV_MAIN1 an INV_MAIN2.
;; They both contain one universal quantifier over array indices.

;; Author: Mattias Ulbrich <ulbrich@kit.edu>
;; As an example interesting for regression verification: http://formal.iti.kit.edu/reve

(set-logic HORN)

;; a n i1 h1 i2 h2 
(declare-fun INV_MAIN_1 (Int Int Int (Array Int Int) Int (Array Int Int)) Bool)

;; (define-fun INV_MAIN_1 ((a Int) (n Int)
;;                         (i$1 Int) (HEAP$1 (Array Int Int))
;;                         (i$2 Int) (HEAP$2 (Array Int Int)))
;;   Bool
;;   (and
;;    (<= 0 i$1)
;;    (<= i$1 n)
;;    (= i$1 i$2)
;;    (forall ((i Int))
;;            (! (=
;;             (select HEAP$2 i)
;;             (ite (and (<= a i) (< i (+ a i$1)))
;;                  (+ 1 (select HEAP$1 i))
;;                  (select HEAP$1 i)))
;;            :pattern ((select HEAP$2 i)(select HEAP$1 i))
;;            ))))

;; a n i1 s1 h1 i2 s2 h2 
(declare-fun INV_MAIN_2 (Int Int Int Int (Array Int Int) Int Int (Array Int Int)) Bool)

;; (define-fun INV_MAIN_2 ((a Int) (n Int)
;;                         (i$1 Int) (s$1 Int) (HEAP$1 (Array Int Int))
;;                         (i$2 Int) (s$2 Int) (HEAP$2 (Array Int Int)))
;;   Bool
;;   (and
;;    (<= 0 i$1)
;;    (<= i$1 n)
;;    (= i$1 i$2)
;;    (= s$1 s$2)
;;    (forall ((iv Int))
;;            (=
;;             (select HEAP$2 iv)
;;             (ite (and (<= a iv) (< iv (+ a n)))
;;                  (+ 1 (select HEAP$1 iv))
;;                  (select HEAP$1 iv))))))

(declare-fun a () Int)
(declare-fun n () Int)
(declare-fun i$1 () Int)
(declare-fun i$2 () Int)
(declare-fun HEAP$1 () (Array Int  Int))
(declare-fun HEAP$2 () (Array Int  Int))

(assert
   (forall
    ((n Int)
     (a Int)
     (i$1 Int)
     (HEAP$1 (Array Int Int))
     (i$2 Int)
     (HEAP$2 (Array Int Int)))
    
    (=> (and (> n 0) (= HEAP$1 HEAP$2))
       (INV_MAIN_1 a n 0 HEAP$1 0 HEAP$2))))


(assert
   (forall
    ((n Int)
     (a Int)
     (i$1 Int)
     (HEAP$1 (Array Int Int))
     (i$2 Int)
     (HEAP$2 (Array Int Int)))
    (=>
     (INV_MAIN_1 a n i$1 HEAP$1 i$2 HEAP$2)
     (=>
      (< i$1 n)
      (INV_MAIN_1 a n
                  (+ i$1 1) (store HEAP$1 (+ a i$1) (+ (select HEAP$1 (+ a i$1)) 1))
                  (+ i$2 1) (store HEAP$2 (+ a i$1) (+ (select HEAP$2 (+ a i$2)) 2)))))))

(assert
   (forall
    ((n Int)
     (a Int)
     (i$1 Int)
     (HEAP$1 (Array Int Int))
     (i$2 Int)
     (HEAP$2 (Array Int Int)))
    (=>
     (INV_MAIN_1 a n i$1 HEAP$1 i$2 HEAP$2)
     (= (< i$1 n) (< i$2 n)))))

(assert
   (forall
    ((n Int)
     (a Int)
     (i$1 Int)
     (HEAP$1 (Array Int Int))
     (i$2 Int)
     (HEAP$2 (Array Int Int)))
    (=>
     (INV_MAIN_1 a n i$1 HEAP$1 i$2 HEAP$2)
     (=>
      (not (< i$1 n))
      (INV_MAIN_2 a n 0 0 HEAP$1 0 0 HEAP$2)))))

(assert
   (forall
    ((n Int)
     (a Int)
     (i$1 Int)
     (s$1 Int)
     (HEAP$1 (Array Int Int))
     (i$2 Int)
     (s$2 Int)
     (HEAP$2 (Array Int Int)))
    (=>
     (INV_MAIN_2 a n i$1 s$1 HEAP$1 i$2 s$2 HEAP$2)
     (=>
      (< i$1 n)
      (INV_MAIN_2 a n
                  (+ i$1 1) (+ (+ s$1 (select HEAP$1 (+ a i$1))) 1) HEAP$1
                  (+ i$2 1) (+ s$2 (select HEAP$2 (+ a i$2))) HEAP$2)))))

(assert
   (forall
     ((n Int)
     (a Int)
     (i$1 Int)
     (s$1 Int)
     (HEAP$1 (Array Int Int))
     (i$2 Int)
     (s$2 Int)
     (HEAP$2 (Array Int Int)))
    (=>
     (INV_MAIN_2 a n i$1 s$1 HEAP$1 i$2 s$2 HEAP$2)
     (= (< i$1 n) (< i$2 n)))))

(assert
 (forall
    ((n Int)
     (a Int)
     (i$1 Int)
     (s$1 Int)
     (HEAP$1 (Array Int Int))
     (i$2 Int)
     (s$2 Int)
     (HEAP$2 (Array Int Int)))
    (=>
     (INV_MAIN_2 a n i$1 s$1 HEAP$1 i$2 s$2 HEAP$2)
     (=>
      (not (< i$1 n))
      (= s$1 s$2)))))


(check-sat)
(get-model)
