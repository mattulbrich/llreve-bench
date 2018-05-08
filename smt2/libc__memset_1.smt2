;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((dst$1_0 Int)
    (c$1_0 Int)
    (n$1_0 Int)
    (HEAP$1 (Array Int Int))
    (dst$2_0 Int)
    (s$2_0 Int)
    (count$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= dst$1_0 dst$2_0)
      (= c$1_0 s$2_0)
      (= n$1_0 count$2_0)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= result$1 result$2)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))))
; :annot (INV_MAIN_0 c$1_0 d.0$1_0 dst$1_0 n.addr.0$1_0 HEAP$1 a.0$2_0 dec$2_0 dst$2_0 s$2_0 HEAP$2)
(declare-fun
   INV_MAIN_0
   (Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((dst$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (s$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old c$1_0_old n$1_0_old HEAP$1_old dst$2_0_old s$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (distinct n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 dst$1_0)
                      (HEAP$1_res HEAP$1)
                      (dst$2_0 dst$2_0_old)
                      (s$2_0 s$2_0_old)
                      (count$2_0 count$2_0_old))
                     (let
                        ((HEAP$2 HEAP$2_old)
                         (inc$2_0 (+ count$2_0 1)))
                        (let
                           ((count.addr.0$2_0 inc$2_0))
                           (let
                              ((a.0$2_0 dst$2_0)
                               (dec$2_0 (+ count.addr.0$2_0 (- 1))))
                              (let
                                 ((tobool$2_0 (distinct dec$2_0 0)))
                                 (not tobool$2_0))))))))))))
(assert
   (forall
      ((dst$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (s$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old c$1_0_old n$1_0_old HEAP$1_old dst$2_0_old s$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (distinct n$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (d.0$1_0 dst$1_0)
                      (dst$2_0 dst$2_0_old)
                      (s$2_0 s$2_0_old)
                      (count$2_0 count$2_0_old))
                     (let
                        ((HEAP$2 HEAP$2_old)
                         (inc$2_0 (+ count$2_0 1)))
                        (let
                           ((count.addr.0$2_0 inc$2_0))
                           (let
                              ((a.0$2_0 dst$2_0)
                               (dec$2_0 (+ count.addr.0$2_0 (- 1))))
                              (let
                                 ((tobool$2_0 (distinct dec$2_0 0)))
                                 (=>
                                    (not tobool$2_0)
                                    (let
                                       ((result$2 dst$2_0)
                                        (HEAP$2_res HEAP$2))
                                       false)))))))))))))
(assert
   (forall
      ((dst$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (s$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old c$1_0_old n$1_0_old HEAP$1_old dst$2_0_old s$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (distinct n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 dst$1_0)
                      (HEAP$1_res HEAP$1)
                      (dst$2_0 dst$2_0_old)
                      (s$2_0 s$2_0_old)
                      (count$2_0 count$2_0_old))
                     (let
                        ((HEAP$2 HEAP$2_old)
                         (inc$2_0 (+ count$2_0 1)))
                        (let
                           ((count.addr.0$2_0 inc$2_0))
                           (let
                              ((a.0$2_0 dst$2_0)
                               (dec$2_0 (+ count.addr.0$2_0 (- 1))))
                              (let
                                 ((tobool$2_0 (distinct dec$2_0 0)))
                                 (=>
                                    (not tobool$2_0)
                                    (let
                                       ((result$2 dst$2_0)
                                        (HEAP$2_res HEAP$2))
                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))
(assert
   (forall
      ((dst$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (s$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old c$1_0_old n$1_0_old HEAP$1_old dst$2_0_old s$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (distinct n$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (d.0$1_0 dst$1_0)
                      (dst$2_0 dst$2_0_old)
                      (s$2_0 s$2_0_old)
                      (count$2_0 count$2_0_old))
                     (let
                        ((HEAP$2 HEAP$2_old)
                         (inc$2_0 (+ count$2_0 1)))
                        (let
                           ((count.addr.0$2_0 inc$2_0))
                           (let
                              ((a.0$2_0 dst$2_0)
                               (dec$2_0 (+ count.addr.0$2_0 (- 1))))
                              (let
                                 ((tobool$2_0 (distinct dec$2_0 0)))
                                 (=>
                                    tobool$2_0
                                    (forall
                                       ((i1 Int)
                                        (i2 Int))
                                       (INV_MAIN_0 c$1_0 d.0$1_0 dst$1_0 n.addr.0$1_0 i1 (select HEAP$1 i1) a.0$2_0 dec$2_0 dst$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (d.0$1_0_old Int)
       (dst$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (dec$2_0_old Int)
       (dst$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 c$1_0_old d.0$1_0_old dst$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old dec$2_0_old dst$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((c$1_0 c$1_0_old))
            (let
               ((d.0$1_0 d.0$1_0_old)
                (dst$1_0 dst$1_0_old)
                (n.addr.0$1_0 n.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (conv$1_0 c$1_0))
               (let
                  ((incdec.ptr$1_0 (+ d.0$1_0 1))
                   (HEAP$1 (store HEAP$1 d.0$1_0 conv$1_0))
                   (dec$1_0 (+ n.addr.0$1_0 (- 1))))
                  (let
                     ((cmp1$1_0 (distinct dec$1_0 0)))
                     (=>
                        (not cmp1$1_0)
                        (let
                           ((result$1 dst$1_0)
                            (HEAP$1_res HEAP$1)
                            (a.0$2_0 a.0$2_0_old)
                            (dec$2_0 dec$2_0_old)
                            (dst$2_0 dst$2_0_old)
                            (s$2_0 s$2_0_old))
                           (let
                              ((HEAP$2 HEAP$2_old)
                               (conv$2_0 s$2_0))
                              (let
                                 ((incdec.ptr$2_0 (+ a.0$2_0 1))
                                  (HEAP$2 (store HEAP$2 a.0$2_0 conv$2_0))
                                  (count.addr.0$2_0 dec$2_0))
                                 (let
                                    ((a.0$2_0 incdec.ptr$2_0)
                                     (dec$2_0 (+ count.addr.0$2_0 (- 1))))
                                    (let
                                       ((tobool$2_0 (distinct dec$2_0 0)))
                                       (=>
                                          (not tobool$2_0)
                                          (let
                                             ((result$2 dst$2_0)
                                              (HEAP$2_res HEAP$2))
                                             (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (d.0$1_0_old Int)
       (dst$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (dec$2_0_old Int)
       (dst$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 c$1_0_old d.0$1_0_old dst$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old dec$2_0_old dst$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((c$1_0 c$1_0_old))
            (let
               ((d.0$1_0 d.0$1_0_old)
                (dst$1_0 dst$1_0_old)
                (n.addr.0$1_0 n.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (conv$1_0 c$1_0))
               (let
                  ((incdec.ptr$1_0 (+ d.0$1_0 1))
                   (HEAP$1 (store HEAP$1 d.0$1_0 conv$1_0))
                   (dec$1_0 (+ n.addr.0$1_0 (- 1))))
                  (let
                     ((cmp1$1_0 (distinct dec$1_0 0)))
                     (=>
                        cmp1$1_0
                        (let
                           ((n.addr.0$1_0 dec$1_0)
                            (d.0$1_0 incdec.ptr$1_0)
                            (a.0$2_0 a.0$2_0_old)
                            (dec$2_0 dec$2_0_old)
                            (dst$2_0 dst$2_0_old)
                            (s$2_0 s$2_0_old))
                           (let
                              ((HEAP$2 HEAP$2_old)
                               (conv$2_0 s$2_0))
                              (let
                                 ((incdec.ptr$2_0 (+ a.0$2_0 1))
                                  (HEAP$2 (store HEAP$2 a.0$2_0 conv$2_0))
                                  (count.addr.0$2_0 dec$2_0))
                                 (let
                                    ((a.0$2_0 incdec.ptr$2_0)
                                     (dec$2_0 (+ count.addr.0$2_0 (- 1))))
                                    (let
                                       ((tobool$2_0 (distinct dec$2_0 0)))
                                       (=>
                                          tobool$2_0
                                          (forall
                                             ((i1 Int)
                                              (i2 Int))
                                             (INV_MAIN_0 c$1_0 d.0$1_0 dst$1_0 n.addr.0$1_0 i1 (select HEAP$1 i1) a.0$2_0 dec$2_0 dst$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (d.0$1_0_old Int)
       (dst$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (dec$2_0_old Int)
       (dst$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 c$1_0_old d.0$1_0_old dst$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old dec$2_0_old dst$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((c$1_0 c$1_0_old))
            (let
               ((d.0$1_0 d.0$1_0_old)
                (dst$1_0 dst$1_0_old)
                (n.addr.0$1_0 n.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (conv$1_0 c$1_0))
               (let
                  ((incdec.ptr$1_0 (+ d.0$1_0 1))
                   (HEAP$1 (store HEAP$1 d.0$1_0 conv$1_0))
                   (dec$1_0 (+ n.addr.0$1_0 (- 1))))
                  (let
                     ((cmp1$1_0 (distinct dec$1_0 0)))
                     (=>
                        cmp1$1_0
                        (let
                           ((n.addr.0$1_0 dec$1_0)
                            (d.0$1_0 incdec.ptr$1_0))
                           (=>
                              (let
                                 ((a.0$2_0 a.0$2_0_old)
                                  (dec$2_0 dec$2_0_old)
                                  (dst$2_0 dst$2_0_old)
                                  (s$2_0 s$2_0_old))
                                 (let
                                    ((HEAP$2 HEAP$2_old)
                                     (conv$2_0 s$2_0))
                                    (let
                                       ((incdec.ptr$2_0 (+ a.0$2_0 1))
                                        (HEAP$2 (store HEAP$2 a.0$2_0 conv$2_0))
                                        (count.addr.0$2_0 dec$2_0))
                                       (let
                                          ((a.0$2_0 incdec.ptr$2_0)
                                           (dec$2_0 (+ count.addr.0$2_0 (- 1))))
                                          (let
                                             ((tobool$2_0 (distinct dec$2_0 0)))
                                             (not tobool$2_0))))))
                              (forall
                                 ((i1 Int)
                                  (i2_old Int))
                                 (INV_MAIN_0 c$1_0 d.0$1_0 dst$1_0 n.addr.0$1_0 i1 (select HEAP$1 i1) a.0$2_0_old dec$2_0_old dst$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (d.0$1_0_old Int)
       (dst$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (dec$2_0_old Int)
       (dst$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 c$1_0_old d.0$1_0_old dst$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old dec$2_0_old dst$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((a.0$2_0 a.0$2_0_old)
             (dec$2_0 dec$2_0_old)
             (dst$2_0 dst$2_0_old)
             (s$2_0 s$2_0_old))
            (let
               ((HEAP$2 HEAP$2_old)
                (conv$2_0 s$2_0))
               (let
                  ((incdec.ptr$2_0 (+ a.0$2_0 1))
                   (HEAP$2 (store HEAP$2 a.0$2_0 conv$2_0))
                   (count.addr.0$2_0 dec$2_0))
                  (let
                     ((a.0$2_0 incdec.ptr$2_0)
                      (dec$2_0 (+ count.addr.0$2_0 (- 1))))
                     (let
                        ((tobool$2_0 (distinct dec$2_0 0)))
                        (=>
                           tobool$2_0
                           (=>
                              (let
                                 ((c$1_0 c$1_0_old))
                                 (let
                                    ((d.0$1_0 d.0$1_0_old)
                                     (dst$1_0 dst$1_0_old)
                                     (n.addr.0$1_0 n.addr.0$1_0_old)
                                     (HEAP$1 HEAP$1_old)
                                     (conv$1_0 c$1_0))
                                    (let
                                       ((incdec.ptr$1_0 (+ d.0$1_0 1))
                                        (HEAP$1 (store HEAP$1 d.0$1_0 conv$1_0))
                                        (dec$1_0 (+ n.addr.0$1_0 (- 1))))
                                       (let
                                          ((cmp1$1_0 (distinct dec$1_0 0)))
                                          (=>
                                             cmp1$1_0
                                             (let
                                                ((n.addr.0$1_0 dec$1_0)
                                                 (d.0$1_0 incdec.ptr$1_0))
                                                false))))))
                              (forall
                                 ((i1_old Int)
                                  (i2 Int))
                                 (INV_MAIN_0 c$1_0_old d.0$1_0_old dst$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0 dec$2_0 dst$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))
(check-sat)
(get-model)
