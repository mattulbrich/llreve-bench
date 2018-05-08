;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((dst$1_0 Int)
    (src$1_0 Int)
    (c$1_0 Int)
    (count$1_0 Int)
    (HEAP$1 (Array Int Int))
    (t$2_0 Int)
    (f$2_0 Int)
    (c$2_0 Int)
    (n$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= dst$1_0 t$2_0)
      (= src$1_0 f$2_0)
      (= c$1_0 c$2_0)
      (= count$1_0 n$2_0)
      (= HEAP$1 HEAP$2)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= result$1 result$2)
      (= HEAP$1 HEAP$2)))
; :annot (INV_MAIN_0 b.0$1_0 c$1_0 dec$1_0 incdec.ptr$1_0 HEAP$1 conv$2_0 incdec.ptr$2_0 incdec.ptr1$2_0 n.addr.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_0
   (Int
    Int
    Int
    Int
    (Array Int Int)
    Int
    Int
    Int
    Int
    (Array Int Int))
   Bool)
(assert
   (forall
      ((dst$1_0_old Int)
       (src$1_0_old Int)
       (c$1_0_old Int)
       (count$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (t$2_0_old Int)
       (f$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old src$1_0_old c$1_0_old count$1_0_old HEAP$1_old t$2_0_old f$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (src$1_0 src$1_0_old)
             (c$1_0 c$1_0_old)
             (count$1_0 count$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (count.addr.0$1_0 count$1_0))
               (let
                  ((a.0$1_0 dst$1_0)
                   (b.0$1_0 src$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 b.0$1_0)))
                        (let
                           ((incdec.ptr$1_0 (+ a.0$1_0 1))
                            (HEAP$1 (store HEAP$1 a.0$1_0 _$1_0)))
                           (let
                              ((_$1_1 (select HEAP$1 b.0$1_0)))
                              (let
                                 ((conv$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv$1_0 c$1_0)))
                                    (=>
                                       cmp$1_0
                                       (let
                                          ((retval.0$1_0 incdec.ptr$1_0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (t$2_0 t$2_0_old)
                                              (f$2_0 f$2_0_old)
                                              (c$2_0 c$2_0_old)
                                              (n$2_0 n$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (tobool$2_0 (distinct n$2_0 0)))
                                                (=>
                                                   tobool$2_0
                                                   (let
                                                      ((conv$2_0 c$2_0)
                                                       (n.addr.0$2_0 n$2_0)
                                                       (tp.0$2_0 t$2_0)
                                                       (fp.0$2_0 f$2_0))
                                                      (let
                                                         ((incdec.ptr$2_0 (+ fp.0$2_0 1))
                                                          (_$2_0 (select HEAP$2 fp.0$2_0)))
                                                         (let
                                                            ((incdec.ptr1$2_0 (+ tp.0$2_0 1))
                                                             (HEAP$2 (store HEAP$2 tp.0$2_0 _$2_0))
                                                             (conv2$2_0 _$2_0)
                                                             (conv3$2_0 conv$2_0))
                                                            (let
                                                               ((cmp$2_0 (= conv2$2_0 conv3$2_0)))
                                                               (not (not cmp$2_0)))))))))))))))))))))))
(assert
   (forall
      ((dst$1_0_old Int)
       (src$1_0_old Int)
       (c$1_0_old Int)
       (count$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (t$2_0_old Int)
       (f$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old src$1_0_old c$1_0_old count$1_0_old HEAP$1_old t$2_0_old f$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (src$1_0 src$1_0_old)
             (c$1_0 c$1_0_old)
             (count$1_0 count$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (count.addr.0$1_0 count$1_0))
               (let
                  ((a.0$1_0 dst$1_0)
                   (b.0$1_0 src$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     (not tobool$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (t$2_0 t$2_0_old)
                            (f$2_0 f$2_0_old)
                            (c$2_0 c$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((HEAP$2 HEAP$2_old)
                               (tobool$2_0 (distinct n$2_0 0)))
                              (=>
                                 tobool$2_0
                                 (let
                                    ((conv$2_0 c$2_0)
                                     (n.addr.0$2_0 n$2_0)
                                     (tp.0$2_0 t$2_0)
                                     (fp.0$2_0 f$2_0))
                                    (let
                                       ((incdec.ptr$2_0 (+ fp.0$2_0 1))
                                        (_$2_0 (select HEAP$2 fp.0$2_0)))
                                       (let
                                          ((incdec.ptr1$2_0 (+ tp.0$2_0 1))
                                           (HEAP$2 (store HEAP$2 tp.0$2_0 _$2_0))
                                           (conv2$2_0 _$2_0)
                                           (conv3$2_0 conv$2_0))
                                          (let
                                             ((cmp$2_0 (= conv2$2_0 conv3$2_0)))
                                             (not (not cmp$2_0)))))))))))))))))
(assert
   (forall
      ((dst$1_0_old Int)
       (src$1_0_old Int)
       (c$1_0_old Int)
       (count$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (t$2_0_old Int)
       (f$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old src$1_0_old c$1_0_old count$1_0_old HEAP$1_old t$2_0_old f$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (src$1_0 src$1_0_old)
             (c$1_0 c$1_0_old)
             (count$1_0 count$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (count.addr.0$1_0 count$1_0))
               (let
                  ((a.0$1_0 dst$1_0)
                   (b.0$1_0 src$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 b.0$1_0)))
                        (let
                           ((incdec.ptr$1_0 (+ a.0$1_0 1))
                            (HEAP$1 (store HEAP$1 a.0$1_0 _$1_0)))
                           (let
                              ((_$1_1 (select HEAP$1 b.0$1_0)))
                              (let
                                 ((conv$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv$1_0 c$1_0)))
                                    (=>
                                       (not cmp$1_0)
                                       (let
                                          ((t$2_0 t$2_0_old)
                                           (f$2_0 f$2_0_old)
                                           (c$2_0 c$2_0_old)
                                           (n$2_0 n$2_0_old))
                                          (let
                                             ((HEAP$2 HEAP$2_old)
                                              (tobool$2_0 (distinct n$2_0 0)))
                                             (=>
                                                tobool$2_0
                                                (let
                                                   ((conv$2_0 c$2_0)
                                                    (n.addr.0$2_0 n$2_0)
                                                    (tp.0$2_0 t$2_0)
                                                    (fp.0$2_0 f$2_0))
                                                   (let
                                                      ((incdec.ptr$2_0 (+ fp.0$2_0 1))
                                                       (_$2_0 (select HEAP$2 fp.0$2_0)))
                                                      (let
                                                         ((incdec.ptr1$2_0 (+ tp.0$2_0 1))
                                                          (HEAP$2 (store HEAP$2 tp.0$2_0 _$2_0))
                                                          (conv2$2_0 _$2_0)
                                                          (conv3$2_0 conv$2_0))
                                                         (let
                                                            ((cmp$2_0 (= conv2$2_0 conv3$2_0)))
                                                            (=>
                                                               cmp$2_0
                                                               (let
                                                                  ((retval.0$2_0 incdec.ptr1$2_0))
                                                                  (let
                                                                     ((result$2 retval.0$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     false)))))))))))))))))))))))
(assert
   (forall
      ((dst$1_0_old Int)
       (src$1_0_old Int)
       (c$1_0_old Int)
       (count$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (t$2_0_old Int)
       (f$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old src$1_0_old c$1_0_old count$1_0_old HEAP$1_old t$2_0_old f$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (src$1_0 src$1_0_old)
             (c$1_0 c$1_0_old)
             (count$1_0 count$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (count.addr.0$1_0 count$1_0))
               (let
                  ((a.0$1_0 dst$1_0)
                   (b.0$1_0 src$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 b.0$1_0)))
                        (let
                           ((incdec.ptr$1_0 (+ a.0$1_0 1))
                            (HEAP$1 (store HEAP$1 a.0$1_0 _$1_0)))
                           (let
                              ((_$1_1 (select HEAP$1 b.0$1_0)))
                              (let
                                 ((conv$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv$1_0 c$1_0)))
                                    (=>
                                       (not cmp$1_0)
                                       (let
                                          ((t$2_0 t$2_0_old)
                                           (f$2_0 f$2_0_old)
                                           (c$2_0 c$2_0_old)
                                           (n$2_0 n$2_0_old))
                                          (let
                                             ((HEAP$2 HEAP$2_old)
                                              (tobool$2_0 (distinct n$2_0 0)))
                                             (=>
                                                (not tobool$2_0)
                                                (let
                                                   ((retval.0$2_0 0))
                                                   (let
                                                      ((result$2 retval.0$2_0)
                                                       (HEAP$2_res HEAP$2))
                                                      false))))))))))))))))))
(assert
   (forall
      ((dst$1_0_old Int)
       (src$1_0_old Int)
       (c$1_0_old Int)
       (count$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (t$2_0_old Int)
       (f$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old src$1_0_old c$1_0_old count$1_0_old HEAP$1_old t$2_0_old f$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (src$1_0 src$1_0_old)
             (c$1_0 c$1_0_old)
             (count$1_0 count$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (count.addr.0$1_0 count$1_0))
               (let
                  ((a.0$1_0 dst$1_0)
                   (b.0$1_0 src$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 b.0$1_0)))
                        (let
                           ((incdec.ptr$1_0 (+ a.0$1_0 1))
                            (HEAP$1 (store HEAP$1 a.0$1_0 _$1_0)))
                           (let
                              ((_$1_1 (select HEAP$1 b.0$1_0)))
                              (let
                                 ((conv$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv$1_0 c$1_0)))
                                    (=>
                                       cmp$1_0
                                       (let
                                          ((retval.0$1_0 incdec.ptr$1_0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (t$2_0 t$2_0_old)
                                              (f$2_0 f$2_0_old)
                                              (c$2_0 c$2_0_old)
                                              (n$2_0 n$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (tobool$2_0 (distinct n$2_0 0)))
                                                (=>
                                                   tobool$2_0
                                                   (let
                                                      ((conv$2_0 c$2_0)
                                                       (n.addr.0$2_0 n$2_0)
                                                       (tp.0$2_0 t$2_0)
                                                       (fp.0$2_0 f$2_0))
                                                      (let
                                                         ((incdec.ptr$2_0 (+ fp.0$2_0 1))
                                                          (_$2_0 (select HEAP$2 fp.0$2_0)))
                                                         (let
                                                            ((incdec.ptr1$2_0 (+ tp.0$2_0 1))
                                                             (HEAP$2 (store HEAP$2 tp.0$2_0 _$2_0))
                                                             (conv2$2_0 _$2_0)
                                                             (conv3$2_0 conv$2_0))
                                                            (let
                                                               ((cmp$2_0 (= conv2$2_0 conv3$2_0)))
                                                               (=>
                                                                  cmp$2_0
                                                                  (let
                                                                     ((retval.0$2_0 incdec.ptr1$2_0))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((dst$1_0_old Int)
       (src$1_0_old Int)
       (c$1_0_old Int)
       (count$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (t$2_0_old Int)
       (f$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old src$1_0_old c$1_0_old count$1_0_old HEAP$1_old t$2_0_old f$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (src$1_0 src$1_0_old)
             (c$1_0 c$1_0_old)
             (count$1_0 count$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (count.addr.0$1_0 count$1_0))
               (let
                  ((a.0$1_0 dst$1_0)
                   (b.0$1_0 src$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 b.0$1_0)))
                        (let
                           ((incdec.ptr$1_0 (+ a.0$1_0 1))
                            (HEAP$1 (store HEAP$1 a.0$1_0 _$1_0)))
                           (let
                              ((_$1_1 (select HEAP$1 b.0$1_0)))
                              (let
                                 ((conv$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv$1_0 c$1_0)))
                                    (=>
                                       cmp$1_0
                                       (let
                                          ((retval.0$1_0 incdec.ptr$1_0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (t$2_0 t$2_0_old)
                                              (f$2_0 f$2_0_old)
                                              (c$2_0 c$2_0_old)
                                              (n$2_0 n$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (tobool$2_0 (distinct n$2_0 0)))
                                                (=>
                                                   (not tobool$2_0)
                                                   (let
                                                      ((retval.0$2_0 0))
                                                      (let
                                                         ((result$2 retval.0$2_0)
                                                          (HEAP$2_res HEAP$2))
                                                         (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))
(assert
   (forall
      ((dst$1_0_old Int)
       (src$1_0_old Int)
       (c$1_0_old Int)
       (count$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (t$2_0_old Int)
       (f$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old src$1_0_old c$1_0_old count$1_0_old HEAP$1_old t$2_0_old f$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (src$1_0 src$1_0_old)
             (c$1_0 c$1_0_old)
             (count$1_0 count$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (count.addr.0$1_0 count$1_0))
               (let
                  ((a.0$1_0 dst$1_0)
                   (b.0$1_0 src$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     (not tobool$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (t$2_0 t$2_0_old)
                            (f$2_0 f$2_0_old)
                            (c$2_0 c$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((HEAP$2 HEAP$2_old)
                               (tobool$2_0 (distinct n$2_0 0)))
                              (=>
                                 tobool$2_0
                                 (let
                                    ((conv$2_0 c$2_0)
                                     (n.addr.0$2_0 n$2_0)
                                     (tp.0$2_0 t$2_0)
                                     (fp.0$2_0 f$2_0))
                                    (let
                                       ((incdec.ptr$2_0 (+ fp.0$2_0 1))
                                        (_$2_0 (select HEAP$2 fp.0$2_0)))
                                       (let
                                          ((incdec.ptr1$2_0 (+ tp.0$2_0 1))
                                           (HEAP$2 (store HEAP$2 tp.0$2_0 _$2_0))
                                           (conv2$2_0 _$2_0)
                                           (conv3$2_0 conv$2_0))
                                          (let
                                             ((cmp$2_0 (= conv2$2_0 conv3$2_0)))
                                             (=>
                                                cmp$2_0
                                                (let
                                                   ((retval.0$2_0 incdec.ptr1$2_0))
                                                   (let
                                                      ((result$2 retval.0$2_0)
                                                       (HEAP$2_res HEAP$2))
                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))
(assert
   (forall
      ((dst$1_0_old Int)
       (src$1_0_old Int)
       (c$1_0_old Int)
       (count$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (t$2_0_old Int)
       (f$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old src$1_0_old c$1_0_old count$1_0_old HEAP$1_old t$2_0_old f$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (src$1_0 src$1_0_old)
             (c$1_0 c$1_0_old)
             (count$1_0 count$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (count.addr.0$1_0 count$1_0))
               (let
                  ((a.0$1_0 dst$1_0)
                   (b.0$1_0 src$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     (not tobool$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (t$2_0 t$2_0_old)
                            (f$2_0 f$2_0_old)
                            (c$2_0 c$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((HEAP$2 HEAP$2_old)
                               (tobool$2_0 (distinct n$2_0 0)))
                              (=>
                                 (not tobool$2_0)
                                 (let
                                    ((retval.0$2_0 0))
                                    (let
                                       ((result$2 retval.0$2_0)
                                        (HEAP$2_res HEAP$2))
                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))
(assert
   (forall
      ((dst$1_0_old Int)
       (src$1_0_old Int)
       (c$1_0_old Int)
       (count$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (t$2_0_old Int)
       (f$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst$1_0_old src$1_0_old c$1_0_old count$1_0_old HEAP$1_old t$2_0_old f$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((dst$1_0 dst$1_0_old)
             (src$1_0 src$1_0_old)
             (c$1_0 c$1_0_old)
             (count$1_0 count$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (count.addr.0$1_0 count$1_0))
               (let
                  ((a.0$1_0 dst$1_0)
                   (b.0$1_0 src$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 b.0$1_0)))
                        (let
                           ((incdec.ptr$1_0 (+ a.0$1_0 1))
                            (HEAP$1 (store HEAP$1 a.0$1_0 _$1_0)))
                           (let
                              ((_$1_1 (select HEAP$1 b.0$1_0)))
                              (let
                                 ((conv$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv$1_0 c$1_0)))
                                    (=>
                                       (not cmp$1_0)
                                       (let
                                          ((t$2_0 t$2_0_old)
                                           (f$2_0 f$2_0_old)
                                           (c$2_0 c$2_0_old)
                                           (n$2_0 n$2_0_old))
                                          (let
                                             ((HEAP$2 HEAP$2_old)
                                              (tobool$2_0 (distinct n$2_0 0)))
                                             (=>
                                                tobool$2_0
                                                (let
                                                   ((conv$2_0 c$2_0)
                                                    (n.addr.0$2_0 n$2_0)
                                                    (tp.0$2_0 t$2_0)
                                                    (fp.0$2_0 f$2_0))
                                                   (let
                                                      ((incdec.ptr$2_0 (+ fp.0$2_0 1))
                                                       (_$2_0 (select HEAP$2 fp.0$2_0)))
                                                      (let
                                                         ((incdec.ptr1$2_0 (+ tp.0$2_0 1))
                                                          (HEAP$2 (store HEAP$2 tp.0$2_0 _$2_0))
                                                          (conv2$2_0 _$2_0)
                                                          (conv3$2_0 conv$2_0))
                                                         (let
                                                            ((cmp$2_0 (= conv2$2_0 conv3$2_0)))
                                                            (=>
                                                               (not cmp$2_0)
                                                               (INV_MAIN_0 b.0$1_0 c$1_0 dec$1_0 incdec.ptr$1_0 HEAP$1 conv$2_0 incdec.ptr$2_0 incdec.ptr1$2_0 n.addr.0$2_0 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((b.0$1_0_old Int)
       (c$1_0_old Int)
       (dec$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (incdec.ptr1$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 b.0$1_0_old c$1_0_old dec$1_0_old incdec.ptr$1_0_old HEAP$1_old conv$2_0_old incdec.ptr$2_0_old incdec.ptr1$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((b.0$1_0 b.0$1_0_old)
             (c$1_0 c$1_0_old)
             (dec$1_0 dec$1_0_old))
            (let
               ((incdec.ptr$1_0 incdec.ptr$1_0_old)
                (HEAP$1 HEAP$1_old)
                (incdec.ptr2$1_0 (+ b.0$1_0 1))
                (count.addr.0$1_0 dec$1_0))
               (let
                  ((a.0$1_0 incdec.ptr$1_0)
                   (b.0$1_0 incdec.ptr2$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 b.0$1_0)))
                        (let
                           ((incdec.ptr$1_0 (+ a.0$1_0 1))
                            (HEAP$1 (store HEAP$1 a.0$1_0 _$1_0)))
                           (let
                              ((_$1_1 (select HEAP$1 b.0$1_0)))
                              (let
                                 ((conv$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv$1_0 c$1_0)))
                                    (=>
                                       cmp$1_0
                                       (let
                                          ((retval.0$1_0 incdec.ptr$1_0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (conv$2_0 conv$2_0_old)
                                              (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                              (incdec.ptr1$2_0 incdec.ptr1$2_0_old)
                                              (n.addr.0$2_0 n.addr.0$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (dec$2_0 (+ n.addr.0$2_0 (- 1))))
                                                (let
                                                   ((cmp6$2_0 (distinct dec$2_0 0)))
                                                   (=>
                                                      cmp6$2_0
                                                      (let
                                                         ((n.addr.0$2_0 dec$2_0)
                                                          (tp.0$2_0 incdec.ptr1$2_0)
                                                          (fp.0$2_0 incdec.ptr$2_0))
                                                         (let
                                                            ((incdec.ptr$2_0 (+ fp.0$2_0 1))
                                                             (_$2_0 (select HEAP$2 fp.0$2_0)))
                                                            (let
                                                               ((incdec.ptr1$2_0 (+ tp.0$2_0 1))
                                                                (HEAP$2 (store HEAP$2 tp.0$2_0 _$2_0))
                                                                (conv2$2_0 _$2_0)
                                                                (conv3$2_0 conv$2_0))
                                                               (let
                                                                  ((cmp$2_0 (= conv2$2_0 conv3$2_0)))
                                                                  (=>
                                                                     cmp$2_0
                                                                     (let
                                                                        ((retval.0$2_0 incdec.ptr1$2_0))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((b.0$1_0_old Int)
       (c$1_0_old Int)
       (dec$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (incdec.ptr1$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 b.0$1_0_old c$1_0_old dec$1_0_old incdec.ptr$1_0_old HEAP$1_old conv$2_0_old incdec.ptr$2_0_old incdec.ptr1$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((b.0$1_0 b.0$1_0_old)
             (c$1_0 c$1_0_old)
             (dec$1_0 dec$1_0_old))
            (let
               ((incdec.ptr$1_0 incdec.ptr$1_0_old)
                (HEAP$1 HEAP$1_old)
                (incdec.ptr2$1_0 (+ b.0$1_0 1))
                (count.addr.0$1_0 dec$1_0))
               (let
                  ((a.0$1_0 incdec.ptr$1_0)
                   (b.0$1_0 incdec.ptr2$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 b.0$1_0)))
                        (let
                           ((incdec.ptr$1_0 (+ a.0$1_0 1))
                            (HEAP$1 (store HEAP$1 a.0$1_0 _$1_0)))
                           (let
                              ((_$1_1 (select HEAP$1 b.0$1_0)))
                              (let
                                 ((conv$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv$1_0 c$1_0)))
                                    (=>
                                       cmp$1_0
                                       (let
                                          ((retval.0$1_0 incdec.ptr$1_0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (conv$2_0 conv$2_0_old)
                                              (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                              (incdec.ptr1$2_0 incdec.ptr1$2_0_old)
                                              (n.addr.0$2_0 n.addr.0$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (dec$2_0 (+ n.addr.0$2_0 (- 1))))
                                                (let
                                                   ((cmp6$2_0 (distinct dec$2_0 0)))
                                                   (=>
                                                      (not cmp6$2_0)
                                                      (let
                                                         ((retval.0$2_0 0))
                                                         (let
                                                            ((result$2 retval.0$2_0)
                                                             (HEAP$2_res HEAP$2))
                                                            (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))
(assert
   (forall
      ((b.0$1_0_old Int)
       (c$1_0_old Int)
       (dec$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (incdec.ptr1$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 b.0$1_0_old c$1_0_old dec$1_0_old incdec.ptr$1_0_old HEAP$1_old conv$2_0_old incdec.ptr$2_0_old incdec.ptr1$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((b.0$1_0 b.0$1_0_old)
             (c$1_0 c$1_0_old)
             (dec$1_0 dec$1_0_old))
            (let
               ((incdec.ptr$1_0 incdec.ptr$1_0_old)
                (HEAP$1 HEAP$1_old)
                (incdec.ptr2$1_0 (+ b.0$1_0 1))
                (count.addr.0$1_0 dec$1_0))
               (let
                  ((a.0$1_0 incdec.ptr$1_0)
                   (b.0$1_0 incdec.ptr2$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     (not tobool$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (conv$2_0 conv$2_0_old)
                            (incdec.ptr$2_0 incdec.ptr$2_0_old)
                            (incdec.ptr1$2_0 incdec.ptr1$2_0_old)
                            (n.addr.0$2_0 n.addr.0$2_0_old))
                           (let
                              ((HEAP$2 HEAP$2_old)
                               (dec$2_0 (+ n.addr.0$2_0 (- 1))))
                              (let
                                 ((cmp6$2_0 (distinct dec$2_0 0)))
                                 (=>
                                    cmp6$2_0
                                    (let
                                       ((n.addr.0$2_0 dec$2_0)
                                        (tp.0$2_0 incdec.ptr1$2_0)
                                        (fp.0$2_0 incdec.ptr$2_0))
                                       (let
                                          ((incdec.ptr$2_0 (+ fp.0$2_0 1))
                                           (_$2_0 (select HEAP$2 fp.0$2_0)))
                                          (let
                                             ((incdec.ptr1$2_0 (+ tp.0$2_0 1))
                                              (HEAP$2 (store HEAP$2 tp.0$2_0 _$2_0))
                                              (conv2$2_0 _$2_0)
                                              (conv3$2_0 conv$2_0))
                                             (let
                                                ((cmp$2_0 (= conv2$2_0 conv3$2_0)))
                                                (=>
                                                   cmp$2_0
                                                   (let
                                                      ((retval.0$2_0 incdec.ptr1$2_0))
                                                      (let
                                                         ((result$2 retval.0$2_0)
                                                          (HEAP$2_res HEAP$2))
                                                         (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))
(assert
   (forall
      ((b.0$1_0_old Int)
       (c$1_0_old Int)
       (dec$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (incdec.ptr1$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 b.0$1_0_old c$1_0_old dec$1_0_old incdec.ptr$1_0_old HEAP$1_old conv$2_0_old incdec.ptr$2_0_old incdec.ptr1$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((b.0$1_0 b.0$1_0_old)
             (c$1_0 c$1_0_old)
             (dec$1_0 dec$1_0_old))
            (let
               ((incdec.ptr$1_0 incdec.ptr$1_0_old)
                (HEAP$1 HEAP$1_old)
                (incdec.ptr2$1_0 (+ b.0$1_0 1))
                (count.addr.0$1_0 dec$1_0))
               (let
                  ((a.0$1_0 incdec.ptr$1_0)
                   (b.0$1_0 incdec.ptr2$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     (not tobool$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (conv$2_0 conv$2_0_old)
                            (incdec.ptr$2_0 incdec.ptr$2_0_old)
                            (incdec.ptr1$2_0 incdec.ptr1$2_0_old)
                            (n.addr.0$2_0 n.addr.0$2_0_old))
                           (let
                              ((HEAP$2 HEAP$2_old)
                               (dec$2_0 (+ n.addr.0$2_0 (- 1))))
                              (let
                                 ((cmp6$2_0 (distinct dec$2_0 0)))
                                 (=>
                                    (not cmp6$2_0)
                                    (let
                                       ((retval.0$2_0 0))
                                       (let
                                          ((result$2 retval.0$2_0)
                                           (HEAP$2_res HEAP$2))
                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))
(assert
   (forall
      ((b.0$1_0_old Int)
       (c$1_0_old Int)
       (dec$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (incdec.ptr1$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 b.0$1_0_old c$1_0_old dec$1_0_old incdec.ptr$1_0_old HEAP$1_old conv$2_0_old incdec.ptr$2_0_old incdec.ptr1$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((b.0$1_0 b.0$1_0_old)
             (c$1_0 c$1_0_old)
             (dec$1_0 dec$1_0_old))
            (let
               ((incdec.ptr$1_0 incdec.ptr$1_0_old)
                (HEAP$1 HEAP$1_old)
                (incdec.ptr2$1_0 (+ b.0$1_0 1))
                (count.addr.0$1_0 dec$1_0))
               (let
                  ((a.0$1_0 incdec.ptr$1_0)
                   (b.0$1_0 incdec.ptr2$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 b.0$1_0)))
                        (let
                           ((incdec.ptr$1_0 (+ a.0$1_0 1))
                            (HEAP$1 (store HEAP$1 a.0$1_0 _$1_0)))
                           (let
                              ((_$1_1 (select HEAP$1 b.0$1_0)))
                              (let
                                 ((conv$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv$1_0 c$1_0)))
                                    (=>
                                       (not cmp$1_0)
                                       (let
                                          ((conv$2_0 conv$2_0_old)
                                           (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                           (incdec.ptr1$2_0 incdec.ptr1$2_0_old)
                                           (n.addr.0$2_0 n.addr.0$2_0_old))
                                          (let
                                             ((HEAP$2 HEAP$2_old)
                                              (dec$2_0 (+ n.addr.0$2_0 (- 1))))
                                             (let
                                                ((cmp6$2_0 (distinct dec$2_0 0)))
                                                (=>
                                                   cmp6$2_0
                                                   (let
                                                      ((n.addr.0$2_0 dec$2_0)
                                                       (tp.0$2_0 incdec.ptr1$2_0)
                                                       (fp.0$2_0 incdec.ptr$2_0))
                                                      (let
                                                         ((incdec.ptr$2_0 (+ fp.0$2_0 1))
                                                          (_$2_0 (select HEAP$2 fp.0$2_0)))
                                                         (let
                                                            ((incdec.ptr1$2_0 (+ tp.0$2_0 1))
                                                             (HEAP$2 (store HEAP$2 tp.0$2_0 _$2_0))
                                                             (conv2$2_0 _$2_0)
                                                             (conv3$2_0 conv$2_0))
                                                            (let
                                                               ((cmp$2_0 (= conv2$2_0 conv3$2_0)))
                                                               (=>
                                                                  (not cmp$2_0)
                                                                  (INV_MAIN_0 b.0$1_0 c$1_0 dec$1_0 incdec.ptr$1_0 HEAP$1 conv$2_0 incdec.ptr$2_0 incdec.ptr1$2_0 n.addr.0$2_0 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((b.0$1_0_old Int)
       (c$1_0_old Int)
       (dec$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (incdec.ptr1$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 b.0$1_0_old c$1_0_old dec$1_0_old incdec.ptr$1_0_old HEAP$1_old conv$2_0_old incdec.ptr$2_0_old incdec.ptr1$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((b.0$1_0 b.0$1_0_old)
             (c$1_0 c$1_0_old)
             (dec$1_0 dec$1_0_old))
            (let
               ((incdec.ptr$1_0 incdec.ptr$1_0_old)
                (HEAP$1 HEAP$1_old)
                (incdec.ptr2$1_0 (+ b.0$1_0 1))
                (count.addr.0$1_0 dec$1_0))
               (let
                  ((a.0$1_0 incdec.ptr$1_0)
                   (b.0$1_0 incdec.ptr2$1_0)
                   (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct count.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 b.0$1_0)))
                        (let
                           ((incdec.ptr$1_0 (+ a.0$1_0 1))
                            (HEAP$1 (store HEAP$1 a.0$1_0 _$1_0)))
                           (let
                              ((_$1_1 (select HEAP$1 b.0$1_0)))
                              (let
                                 ((conv$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv$1_0 c$1_0)))
                                    (=>
                                       (not cmp$1_0)
                                       (=>
                                          (let
                                             ((conv$2_0 conv$2_0_old)
                                              (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                              (incdec.ptr1$2_0 incdec.ptr1$2_0_old)
                                              (n.addr.0$2_0 n.addr.0$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (dec$2_0 (+ n.addr.0$2_0 (- 1))))
                                                (let
                                                   ((cmp6$2_0 (distinct dec$2_0 0)))
                                                   (=>
                                                      cmp6$2_0
                                                      (let
                                                         ((n.addr.0$2_0 dec$2_0)
                                                          (tp.0$2_0 incdec.ptr1$2_0)
                                                          (fp.0$2_0 incdec.ptr$2_0))
                                                         (let
                                                            ((incdec.ptr$2_0 (+ fp.0$2_0 1))
                                                             (_$2_0 (select HEAP$2 fp.0$2_0)))
                                                            (let
                                                               ((incdec.ptr1$2_0 (+ tp.0$2_0 1))
                                                                (HEAP$2 (store HEAP$2 tp.0$2_0 _$2_0))
                                                                (conv2$2_0 _$2_0)
                                                                (conv3$2_0 conv$2_0))
                                                               (let
                                                                  ((cmp$2_0 (= conv2$2_0 conv3$2_0)))
                                                                  (not (not cmp$2_0))))))))))
                                          (INV_MAIN_0 b.0$1_0 c$1_0 dec$1_0 incdec.ptr$1_0 HEAP$1 conv$2_0_old incdec.ptr$2_0_old incdec.ptr1$2_0_old n.addr.0$2_0_old HEAP$2_old)))))))))))))))
(assert
   (forall
      ((b.0$1_0_old Int)
       (c$1_0_old Int)
       (dec$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (incdec.ptr1$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 b.0$1_0_old c$1_0_old dec$1_0_old incdec.ptr$1_0_old HEAP$1_old conv$2_0_old incdec.ptr$2_0_old incdec.ptr1$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((conv$2_0 conv$2_0_old)
             (incdec.ptr$2_0 incdec.ptr$2_0_old)
             (incdec.ptr1$2_0 incdec.ptr1$2_0_old)
             (n.addr.0$2_0 n.addr.0$2_0_old))
            (let
               ((HEAP$2 HEAP$2_old)
                (dec$2_0 (+ n.addr.0$2_0 (- 1))))
               (let
                  ((cmp6$2_0 (distinct dec$2_0 0)))
                  (=>
                     cmp6$2_0
                     (let
                        ((n.addr.0$2_0 dec$2_0)
                         (tp.0$2_0 incdec.ptr1$2_0)
                         (fp.0$2_0 incdec.ptr$2_0))
                        (let
                           ((incdec.ptr$2_0 (+ fp.0$2_0 1))
                            (_$2_0 (select HEAP$2 fp.0$2_0)))
                           (let
                              ((incdec.ptr1$2_0 (+ tp.0$2_0 1))
                               (HEAP$2 (store HEAP$2 tp.0$2_0 _$2_0))
                               (conv2$2_0 _$2_0)
                               (conv3$2_0 conv$2_0))
                              (let
                                 ((cmp$2_0 (= conv2$2_0 conv3$2_0)))
                                 (=>
                                    (not cmp$2_0)
                                    (=>
                                       (let
                                          ((b.0$1_0 b.0$1_0_old)
                                           (c$1_0 c$1_0_old)
                                           (dec$1_0 dec$1_0_old))
                                          (let
                                             ((incdec.ptr$1_0 incdec.ptr$1_0_old)
                                              (HEAP$1 HEAP$1_old)
                                              (incdec.ptr2$1_0 (+ b.0$1_0 1))
                                              (count.addr.0$1_0 dec$1_0))
                                             (let
                                                ((a.0$1_0 incdec.ptr$1_0)
                                                 (b.0$1_0 incdec.ptr2$1_0)
                                                 (dec$1_0 (+ count.addr.0$1_0 (- 1)))
                                                 (tobool$1_0 (distinct count.addr.0$1_0 0)))
                                                (=>
                                                   tobool$1_0
                                                   (let
                                                      ((_$1_0 (select HEAP$1 b.0$1_0)))
                                                      (let
                                                         ((incdec.ptr$1_0 (+ a.0$1_0 1))
                                                          (HEAP$1 (store HEAP$1 a.0$1_0 _$1_0)))
                                                         (let
                                                            ((_$1_1 (select HEAP$1 b.0$1_0)))
                                                            (let
                                                               ((conv$1_0 _$1_1))
                                                               (let
                                                                  ((cmp$1_0 (= conv$1_0 c$1_0)))
                                                                  (not (not cmp$1_0)))))))))))
                                       (INV_MAIN_0 b.0$1_0_old c$1_0_old dec$1_0_old incdec.ptr$1_0_old HEAP$1_old conv$2_0 incdec.ptr$2_0 incdec.ptr1$2_0 n.addr.0$2_0 HEAP$2))))))))))))))
(check-sat)
(get-model)
