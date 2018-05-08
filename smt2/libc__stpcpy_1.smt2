;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((dst$1_0 Int)
    (src$1_0 Int)
    (HEAP$1 (Array Int Int))
    (to$2_0 Int)
    (from$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= dst$1_0 to$2_0)
      (= src$1_0 from$2_0)
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
; :annot (INV_MAIN_0 dst.addr.0$1_0 src.addr.0$1_0 HEAP$1 from.addr.0$2_0 to.addr.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_0
   (Int
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
       (src$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (to$2_0_old Int)
       (from$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old src$1_0_old HEAP$1_old to$2_0_old from$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (src$1_0 src$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (src.addr.0$1_0 src$1_0)
                (dst.addr.0$1_0 dst$1_0)
                (to$2_0 to$2_0_old)
                (from$2_0 from$2_0_old))
               (let
                  ((HEAP$2 HEAP$2_old)
                   (from.addr.0$2_0 from$2_0)
                   (to.addr.0$2_0 to$2_0))
                  (forall
                     ((i1 Int)
                      (i2 Int))
                     (INV_MAIN_0 dst.addr.0$1_0 src.addr.0$1_0 i1 (select HEAP$1 i1) from.addr.0$2_0 to.addr.0$2_0 i2 (select HEAP$2 i2)))))))))
(assert
   (forall
      ((dst.addr.0$1_0_old Int)
       (src.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (from.addr.0$2_0_old Int)
       (to.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 dst.addr.0$1_0_old src.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) from.addr.0$2_0_old to.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((dst.addr.0$1_0 dst.addr.0$1_0_old)
             (src.addr.0$1_0 src.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((incdec.ptr$1_0 (+ src.addr.0$1_0 1))
                (_$1_0 (select HEAP$1 src.addr.0$1_0)))
               (let
                  ((incdec.ptr1$1_0 (+ dst.addr.0$1_0 1))
                   (HEAP$1 (store HEAP$1 dst.addr.0$1_0 _$1_0))
                   (conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        (not tobool$1_0)
                        (let
                           ((add.ptr$1_0 (+ incdec.ptr1$1_0 (- 1))))
                           (let
                              ((result$1 add.ptr$1_0)
                               (HEAP$1_res HEAP$1)
                               (from.addr.0$2_0 from.addr.0$2_0_old)
                               (to.addr.0$2_0 to.addr.0$2_0_old)
                               (HEAP$2 HEAP$2_old))
                              (let
                                 ((_$2_0 (select HEAP$2 from.addr.0$2_0)))
                                 (let
                                    ((HEAP$2 (store HEAP$2 to.addr.0$2_0 _$2_0))
                                     (conv$2_0 _$2_0))
                                    (let
                                       ((cmp$2_0 (distinct conv$2_0 0)))
                                       (=>
                                          (not cmp$2_0)
                                          (let
                                             ((result$2 to.addr.0$2_0)
                                              (HEAP$2_res HEAP$2))
                                             (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))
(assert
   (forall
      ((dst.addr.0$1_0_old Int)
       (src.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (from.addr.0$2_0_old Int)
       (to.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 dst.addr.0$1_0_old src.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) from.addr.0$2_0_old to.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((dst.addr.0$1_0 dst.addr.0$1_0_old)
             (src.addr.0$1_0 src.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((incdec.ptr$1_0 (+ src.addr.0$1_0 1))
                (_$1_0 (select HEAP$1 src.addr.0$1_0)))
               (let
                  ((incdec.ptr1$1_0 (+ dst.addr.0$1_0 1))
                   (HEAP$1 (store HEAP$1 dst.addr.0$1_0 _$1_0))
                   (conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        tobool$1_0
                        (let
                           ((src.addr.0$1_0 incdec.ptr$1_0)
                            (dst.addr.0$1_0 incdec.ptr1$1_0)
                            (from.addr.0$2_0 from.addr.0$2_0_old)
                            (to.addr.0$2_0 to.addr.0$2_0_old)
                            (HEAP$2 HEAP$2_old))
                           (let
                              ((_$2_0 (select HEAP$2 from.addr.0$2_0)))
                              (let
                                 ((HEAP$2 (store HEAP$2 to.addr.0$2_0 _$2_0))
                                  (conv$2_0 _$2_0))
                                 (let
                                    ((cmp$2_0 (distinct conv$2_0 0)))
                                    (=>
                                       cmp$2_0
                                       (let
                                          ((incdec.ptr$2_0 (+ from.addr.0$2_0 1))
                                           (incdec.ptr2$2_0 (+ to.addr.0$2_0 1)))
                                          (let
                                             ((from.addr.0$2_0 incdec.ptr$2_0)
                                              (to.addr.0$2_0 incdec.ptr2$2_0))
                                             (forall
                                                ((i1 Int)
                                                 (i2 Int))
                                                (INV_MAIN_0 dst.addr.0$1_0 src.addr.0$1_0 i1 (select HEAP$1 i1) from.addr.0$2_0 to.addr.0$2_0 i2 (select HEAP$2 i2))))))))))))))))))
(assert
   (forall
      ((dst.addr.0$1_0_old Int)
       (src.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (from.addr.0$2_0_old Int)
       (to.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 dst.addr.0$1_0_old src.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) from.addr.0$2_0_old to.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((dst.addr.0$1_0 dst.addr.0$1_0_old)
             (src.addr.0$1_0 src.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((incdec.ptr$1_0 (+ src.addr.0$1_0 1))
                (_$1_0 (select HEAP$1 src.addr.0$1_0)))
               (let
                  ((incdec.ptr1$1_0 (+ dst.addr.0$1_0 1))
                   (HEAP$1 (store HEAP$1 dst.addr.0$1_0 _$1_0))
                   (conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        tobool$1_0
                        (let
                           ((src.addr.0$1_0 incdec.ptr$1_0)
                            (dst.addr.0$1_0 incdec.ptr1$1_0))
                           (=>
                              (let
                                 ((from.addr.0$2_0 from.addr.0$2_0_old)
                                  (to.addr.0$2_0 to.addr.0$2_0_old)
                                  (HEAP$2 HEAP$2_old))
                                 (let
                                    ((_$2_0 (select HEAP$2 from.addr.0$2_0)))
                                    (let
                                       ((HEAP$2 (store HEAP$2 to.addr.0$2_0 _$2_0))
                                        (conv$2_0 _$2_0))
                                       (let
                                          ((cmp$2_0 (distinct conv$2_0 0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((incdec.ptr$2_0 (+ from.addr.0$2_0 1))
                                                 (incdec.ptr2$2_0 (+ to.addr.0$2_0 1)))
                                                (let
                                                   ((from.addr.0$2_0 incdec.ptr$2_0)
                                                    (to.addr.0$2_0 incdec.ptr2$2_0))
                                                   false)))))))
                              (forall
                                 ((i1 Int)
                                  (i2_old Int))
                                 (INV_MAIN_0 dst.addr.0$1_0 src.addr.0$1_0 i1 (select HEAP$1 i1) from.addr.0$2_0_old to.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))
(assert
   (forall
      ((dst.addr.0$1_0_old Int)
       (src.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (from.addr.0$2_0_old Int)
       (to.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 dst.addr.0$1_0_old src.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) from.addr.0$2_0_old to.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((from.addr.0$2_0 from.addr.0$2_0_old)
             (to.addr.0$2_0 to.addr.0$2_0_old)
             (HEAP$2 HEAP$2_old))
            (let
               ((_$2_0 (select HEAP$2 from.addr.0$2_0)))
               (let
                  ((HEAP$2 (store HEAP$2 to.addr.0$2_0 _$2_0))
                   (conv$2_0 _$2_0))
                  (let
                     ((cmp$2_0 (distinct conv$2_0 0)))
                     (=>
                        cmp$2_0
                        (let
                           ((incdec.ptr$2_0 (+ from.addr.0$2_0 1))
                            (incdec.ptr2$2_0 (+ to.addr.0$2_0 1)))
                           (let
                              ((from.addr.0$2_0 incdec.ptr$2_0)
                               (to.addr.0$2_0 incdec.ptr2$2_0))
                              (=>
                                 (let
                                    ((dst.addr.0$1_0 dst.addr.0$1_0_old)
                                     (src.addr.0$1_0 src.addr.0$1_0_old)
                                     (HEAP$1 HEAP$1_old))
                                    (let
                                       ((incdec.ptr$1_0 (+ src.addr.0$1_0 1))
                                        (_$1_0 (select HEAP$1 src.addr.0$1_0)))
                                       (let
                                          ((incdec.ptr1$1_0 (+ dst.addr.0$1_0 1))
                                           (HEAP$1 (store HEAP$1 dst.addr.0$1_0 _$1_0))
                                           (conv$1_0 _$1_0))
                                          (let
                                             ((tobool$1_0 (distinct conv$1_0 0)))
                                             (=>
                                                tobool$1_0
                                                (let
                                                   ((src.addr.0$1_0 incdec.ptr$1_0)
                                                    (dst.addr.0$1_0 incdec.ptr1$1_0))
                                                   false))))))
                                 (forall
                                    ((i1_old Int)
                                     (i2 Int))
                                    (INV_MAIN_0 dst.addr.0$1_0_old src.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) from.addr.0$2_0 to.addr.0$2_0 i2 (select HEAP$2 i2))))))))))))))
(check-sat)
(get-model)
