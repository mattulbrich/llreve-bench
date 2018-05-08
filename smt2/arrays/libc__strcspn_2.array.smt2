;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((s$1_0 Int)
    (reject$1_0 Int)
    (HEAP$1 (Array Int Int))
    (s$2_0 Int)
    (reject$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= s$1_0 s$2_0)
      (= reject$1_0 reject$2_0)
      (> reject$1_0 0)
      (forall
         ((i_0 Int))
         (= (select HEAP$1 i_0) (select HEAP$2 i_0)))))
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
; :annot (INV_MAIN_0 conv.i$1_0 count.0$1_0 incdec.ptr$1_0 reject$1_0 t.addr.i.0$1_0 HEAP$1 _$2_1 count.0$2_0 incdec.ptr$2_0 reject$2_0 t.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_0
   (Int
    Int
    Int
    Int
    Int
    (Array Int Int)
    Int
    Int
    Int
    Int
    Int
    (Array Int Int))
   Bool)
; :annot (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 HEAP$1 count.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_1
   (Int
    Int
    Int
    (Array Int Int)
    Int
    Int
    Int
    (Array Int Int))
   Bool)
(assert
   (forall
      ((s$1_0_old Int)
       (reject$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s$2_0_old Int)
       (reject$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old reject$1_0_old HEAP$1_old s$2_0_old reject$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old))
            (let
               ((reject$1_0 reject$1_0_old)
                (HEAP$1 HEAP$1_old)
                (s.addr.0$1_0 s$1_0)
                (count.0$1_0 0)
                (s$2_0 s$2_0_old))
               (let
                  ((reject$2_0 reject$2_0_old)
                   (HEAP$2 HEAP$2_old)
                   (count.0$2_0 0)
                   (s.addr.0$2_0 s$2_0))
                  (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 HEAP$1 count.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2)))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           cmp.i$1_0
                           (let
                              ((retval.i.0$1_0 t.addr.i.0$1_0))
                              (let
                                 ((cmp$1_0 (= retval.i.0$1_0 0)))
                                 (=>
                                    (not cmp$1_0)
                                    (let
                                       ((result$1 count.0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (_$2_1 _$2_1_old)
                                        (count.0$2_0 count.0$2_0_old)
                                        (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                        (reject$2_0 reject$2_0_old)
                                        (t.0$2_0 t.0$2_0_old)
                                        (HEAP$2 HEAP$2_old)
                                        (tobool2$2_0 (distinct 1 0)))
                                       (=>
                                          tobool2$2_0
                                          (let
                                             ((_$2_2 (select HEAP$2 t.0$2_0)))
                                             (let
                                                ((conv3$2_0 _$2_2)
                                                 (conv4$2_0 _$2_1))
                                                (let
                                                   ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                                   (=>
                                                      (not cmp$2_0)
                                                      (let
                                                         ((_$2_3 (select HEAP$2 t.0$2_0)))
                                                         (let
                                                            ((tobool6$2_0 (distinct _$2_3 0)))
                                                            (=>
                                                               (not tobool6$2_0)
                                                               (let
                                                                  ((inc$2_0 (+ count.0$2_0 1)))
                                                                  (let
                                                                     ((count.0$2_0 inc$2_0)
                                                                      (s.addr.0$2_0 incdec.ptr$2_0))
                                                                     false)))))))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           cmp.i$1_0
                           (let
                              ((retval.i.0$1_0 t.addr.i.0$1_0))
                              (let
                                 ((cmp$1_0 (= retval.i.0$1_0 0)))
                                 (=>
                                    (not cmp$1_0)
                                    (let
                                       ((result$1 count.0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (_$2_1 _$2_1_old)
                                        (count.0$2_0 count.0$2_0_old)
                                        (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                        (reject$2_0 reject$2_0_old)
                                        (t.0$2_0 t.0$2_0_old)
                                        (HEAP$2 HEAP$2_old)
                                        (tobool2$2_0 (distinct 1 0)))
                                       (=>
                                          (not tobool2$2_0)
                                          (let
                                             ((count.0$2_0 count.0$2_0)
                                              (s.addr.0$2_0 incdec.ptr$2_0))
                                             false)))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           (not cmp.i$1_0)
                           (let
                              ((_$1_3 (select HEAP$1 t.addr.i.0$1_0)))
                              (let
                                 ((tobool4.i$1_0 (distinct _$1_3 0)))
                                 (=>
                                    (not tobool4.i$1_0)
                                    (let
                                       ((retval.i.0$1_0 0))
                                       (let
                                          ((cmp$1_0 (= retval.i.0$1_0 0)))
                                          (=>
                                             (not cmp$1_0)
                                             (let
                                                ((result$1 count.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (_$2_1 _$2_1_old)
                                                 (count.0$2_0 count.0$2_0_old)
                                                 (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                 (reject$2_0 reject$2_0_old)
                                                 (t.0$2_0 t.0$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (tobool2$2_0 (distinct 1 0)))
                                                (=>
                                                   tobool2$2_0
                                                   (let
                                                      ((_$2_2 (select HEAP$2 t.0$2_0)))
                                                      (let
                                                         ((conv3$2_0 _$2_2)
                                                          (conv4$2_0 _$2_1))
                                                         (let
                                                            ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                                            (=>
                                                               (not cmp$2_0)
                                                               (let
                                                                  ((_$2_3 (select HEAP$2 t.0$2_0)))
                                                                  (let
                                                                     ((tobool6$2_0 (distinct _$2_3 0)))
                                                                     (=>
                                                                        (not tobool6$2_0)
                                                                        (let
                                                                           ((inc$2_0 (+ count.0$2_0 1)))
                                                                           (let
                                                                              ((count.0$2_0 inc$2_0)
                                                                               (s.addr.0$2_0 incdec.ptr$2_0))
                                                                              false))))))))))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           (not cmp.i$1_0)
                           (let
                              ((_$1_3 (select HEAP$1 t.addr.i.0$1_0)))
                              (let
                                 ((tobool4.i$1_0 (distinct _$1_3 0)))
                                 (=>
                                    (not tobool4.i$1_0)
                                    (let
                                       ((retval.i.0$1_0 0))
                                       (let
                                          ((cmp$1_0 (= retval.i.0$1_0 0)))
                                          (=>
                                             (not cmp$1_0)
                                             (let
                                                ((result$1 count.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (_$2_1 _$2_1_old)
                                                 (count.0$2_0 count.0$2_0_old)
                                                 (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                 (reject$2_0 reject$2_0_old)
                                                 (t.0$2_0 t.0$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (tobool2$2_0 (distinct 1 0)))
                                                (=>
                                                   (not tobool2$2_0)
                                                   (let
                                                      ((count.0$2_0 count.0$2_0)
                                                       (s.addr.0$2_0 incdec.ptr$2_0))
                                                      false))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               (not tobool.i$1_0)
               (let
                  ((retval.i.0$1_0 t.addr.i.0$1_0))
                  (let
                     ((cmp$1_0 (= retval.i.0$1_0 0)))
                     (=>
                        (not cmp$1_0)
                        (let
                           ((result$1 count.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (_$2_1 _$2_1_old)
                            (count.0$2_0 count.0$2_0_old)
                            (incdec.ptr$2_0 incdec.ptr$2_0_old)
                            (reject$2_0 reject$2_0_old)
                            (t.0$2_0 t.0$2_0_old)
                            (HEAP$2 HEAP$2_old)
                            (tobool2$2_0 (distinct 1 0)))
                           (=>
                              tobool2$2_0
                              (let
                                 ((_$2_2 (select HEAP$2 t.0$2_0)))
                                 (let
                                    ((conv3$2_0 _$2_2)
                                     (conv4$2_0 _$2_1))
                                    (let
                                       ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                       (=>
                                          (not cmp$2_0)
                                          (let
                                             ((_$2_3 (select HEAP$2 t.0$2_0)))
                                             (let
                                                ((tobool6$2_0 (distinct _$2_3 0)))
                                                (=>
                                                   (not tobool6$2_0)
                                                   (let
                                                      ((inc$2_0 (+ count.0$2_0 1)))
                                                      (let
                                                         ((count.0$2_0 inc$2_0)
                                                          (s.addr.0$2_0 incdec.ptr$2_0))
                                                         false)))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               (not tobool.i$1_0)
               (let
                  ((retval.i.0$1_0 t.addr.i.0$1_0))
                  (let
                     ((cmp$1_0 (= retval.i.0$1_0 0)))
                     (=>
                        (not cmp$1_0)
                        (let
                           ((result$1 count.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (_$2_1 _$2_1_old)
                            (count.0$2_0 count.0$2_0_old)
                            (incdec.ptr$2_0 incdec.ptr$2_0_old)
                            (reject$2_0 reject$2_0_old)
                            (t.0$2_0 t.0$2_0_old)
                            (HEAP$2 HEAP$2_old)
                            (tobool2$2_0 (distinct 1 0)))
                           (=>
                              (not tobool2$2_0)
                              (let
                                 ((count.0$2_0 count.0$2_0)
                                  (s.addr.0$2_0 incdec.ptr$2_0))
                                 false)))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           cmp.i$1_0
                           (let
                              ((retval.i.0$1_0 t.addr.i.0$1_0))
                              (let
                                 ((cmp$1_0 (= retval.i.0$1_0 0)))
                                 (=>
                                    cmp$1_0
                                    (let
                                       ((inc$1_0 (+ count.0$1_0 1)))
                                       (let
                                          ((s.addr.0$1_0 incdec.ptr$1_0)
                                           (count.0$1_0 inc$1_0)
                                           (_$2_1 _$2_1_old)
                                           (count.0$2_0 count.0$2_0_old)
                                           (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                           (reject$2_0 reject$2_0_old)
                                           (t.0$2_0 t.0$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (tobool2$2_0 (distinct 1 0)))
                                          (=>
                                             tobool2$2_0
                                             (let
                                                ((_$2_2 (select HEAP$2 t.0$2_0)))
                                                (let
                                                   ((conv3$2_0 _$2_2)
                                                    (conv4$2_0 _$2_1))
                                                   (let
                                                      ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((result$2 count.0$2_0)
                                                             (HEAP$2_res HEAP$2))
                                                            false))))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           (not cmp.i$1_0)
                           (let
                              ((_$1_3 (select HEAP$1 t.addr.i.0$1_0)))
                              (let
                                 ((tobool4.i$1_0 (distinct _$1_3 0)))
                                 (=>
                                    (not tobool4.i$1_0)
                                    (let
                                       ((retval.i.0$1_0 0))
                                       (let
                                          ((cmp$1_0 (= retval.i.0$1_0 0)))
                                          (=>
                                             cmp$1_0
                                             (let
                                                ((inc$1_0 (+ count.0$1_0 1)))
                                                (let
                                                   ((s.addr.0$1_0 incdec.ptr$1_0)
                                                    (count.0$1_0 inc$1_0)
                                                    (_$2_1 _$2_1_old)
                                                    (count.0$2_0 count.0$2_0_old)
                                                    (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                    (reject$2_0 reject$2_0_old)
                                                    (t.0$2_0 t.0$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (tobool2$2_0 (distinct 1 0)))
                                                   (=>
                                                      tobool2$2_0
                                                      (let
                                                         ((_$2_2 (select HEAP$2 t.0$2_0)))
                                                         (let
                                                            ((conv3$2_0 _$2_2)
                                                             (conv4$2_0 _$2_1))
                                                            (let
                                                               ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                                               (=>
                                                                  cmp$2_0
                                                                  (let
                                                                     ((result$2 count.0$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     false)))))))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               (not tobool.i$1_0)
               (let
                  ((retval.i.0$1_0 t.addr.i.0$1_0))
                  (let
                     ((cmp$1_0 (= retval.i.0$1_0 0)))
                     (=>
                        cmp$1_0
                        (let
                           ((inc$1_0 (+ count.0$1_0 1)))
                           (let
                              ((s.addr.0$1_0 incdec.ptr$1_0)
                               (count.0$1_0 inc$1_0)
                               (_$2_1 _$2_1_old)
                               (count.0$2_0 count.0$2_0_old)
                               (incdec.ptr$2_0 incdec.ptr$2_0_old)
                               (reject$2_0 reject$2_0_old)
                               (t.0$2_0 t.0$2_0_old)
                               (HEAP$2 HEAP$2_old)
                               (tobool2$2_0 (distinct 1 0)))
                              (=>
                                 tobool2$2_0
                                 (let
                                    ((_$2_2 (select HEAP$2 t.0$2_0)))
                                    (let
                                       ((conv3$2_0 _$2_2)
                                        (conv4$2_0 _$2_1))
                                       (let
                                          ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((result$2 count.0$2_0)
                                                 (HEAP$2_res HEAP$2))
                                                false))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           cmp.i$1_0
                           (let
                              ((retval.i.0$1_0 t.addr.i.0$1_0))
                              (let
                                 ((cmp$1_0 (= retval.i.0$1_0 0)))
                                 (=>
                                    (not cmp$1_0)
                                    (let
                                       ((result$1 count.0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (_$2_1 _$2_1_old)
                                        (count.0$2_0 count.0$2_0_old)
                                        (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                        (reject$2_0 reject$2_0_old)
                                        (t.0$2_0 t.0$2_0_old)
                                        (HEAP$2 HEAP$2_old)
                                        (tobool2$2_0 (distinct 1 0)))
                                       (=>
                                          tobool2$2_0
                                          (let
                                             ((_$2_2 (select HEAP$2 t.0$2_0)))
                                             (let
                                                ((conv3$2_0 _$2_2)
                                                 (conv4$2_0 _$2_1))
                                                (let
                                                   ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                                   (=>
                                                      cmp$2_0
                                                      (let
                                                         ((result$2 count.0$2_0)
                                                          (HEAP$2_res HEAP$2))
                                                         (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           (not cmp.i$1_0)
                           (let
                              ((_$1_3 (select HEAP$1 t.addr.i.0$1_0)))
                              (let
                                 ((tobool4.i$1_0 (distinct _$1_3 0)))
                                 (=>
                                    (not tobool4.i$1_0)
                                    (let
                                       ((retval.i.0$1_0 0))
                                       (let
                                          ((cmp$1_0 (= retval.i.0$1_0 0)))
                                          (=>
                                             (not cmp$1_0)
                                             (let
                                                ((result$1 count.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (_$2_1 _$2_1_old)
                                                 (count.0$2_0 count.0$2_0_old)
                                                 (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                 (reject$2_0 reject$2_0_old)
                                                 (t.0$2_0 t.0$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (tobool2$2_0 (distinct 1 0)))
                                                (=>
                                                   tobool2$2_0
                                                   (let
                                                      ((_$2_2 (select HEAP$2 t.0$2_0)))
                                                      (let
                                                         ((conv3$2_0 _$2_2)
                                                          (conv4$2_0 _$2_1))
                                                         (let
                                                            ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                                            (=>
                                                               cmp$2_0
                                                               (let
                                                                  ((result$2 count.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               (not tobool.i$1_0)
               (let
                  ((retval.i.0$1_0 t.addr.i.0$1_0))
                  (let
                     ((cmp$1_0 (= retval.i.0$1_0 0)))
                     (=>
                        (not cmp$1_0)
                        (let
                           ((result$1 count.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (_$2_1 _$2_1_old)
                            (count.0$2_0 count.0$2_0_old)
                            (incdec.ptr$2_0 incdec.ptr$2_0_old)
                            (reject$2_0 reject$2_0_old)
                            (t.0$2_0 t.0$2_0_old)
                            (HEAP$2 HEAP$2_old)
                            (tobool2$2_0 (distinct 1 0)))
                           (=>
                              tobool2$2_0
                              (let
                                 ((_$2_2 (select HEAP$2 t.0$2_0)))
                                 (let
                                    ((conv3$2_0 _$2_2)
                                     (conv4$2_0 _$2_1))
                                    (let
                                       ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                       (=>
                                          cmp$2_0
                                          (let
                                             ((result$2 count.0$2_0)
                                              (HEAP$2_res HEAP$2))
                                             (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           (not cmp.i$1_0)
                           (let
                              ((_$1_3 (select HEAP$1 t.addr.i.0$1_0)))
                              (let
                                 ((tobool4.i$1_0 (distinct _$1_3 0)))
                                 (=>
                                    tobool4.i$1_0
                                    (let
                                       ((incdec.ptr.i$1_0 (+ t.addr.i.0$1_0 1)))
                                       (let
                                          ((t.addr.i.0$1_0 incdec.ptr.i$1_0)
                                           (_$2_1 _$2_1_old)
                                           (count.0$2_0 count.0$2_0_old)
                                           (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                           (reject$2_0 reject$2_0_old)
                                           (t.0$2_0 t.0$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (tobool2$2_0 (distinct 1 0)))
                                          (=>
                                             tobool2$2_0
                                             (let
                                                ((_$2_2 (select HEAP$2 t.0$2_0)))
                                                (let
                                                   ((conv3$2_0 _$2_2)
                                                    (conv4$2_0 _$2_1))
                                                   (let
                                                      ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                                      (=>
                                                         (not cmp$2_0)
                                                         (let
                                                            ((_$2_3 (select HEAP$2 t.0$2_0)))
                                                            (let
                                                               ((tobool6$2_0 (distinct _$2_3 0)))
                                                               (=>
                                                                  tobool6$2_0
                                                                  (let
                                                                     ((incdec.ptr9$2_0 (+ t.0$2_0 1)))
                                                                     (let
                                                                        ((t.0$2_0 incdec.ptr9$2_0))
                                                                        (INV_MAIN_0 conv.i$1_0 count.0$1_0 incdec.ptr$1_0 reject$1_0 t.addr.i.0$1_0 HEAP$1 _$2_1 count.0$2_0 incdec.ptr$2_0 reject$2_0 t.0$2_0 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           (not cmp.i$1_0)
                           (let
                              ((_$1_3 (select HEAP$1 t.addr.i.0$1_0)))
                              (let
                                 ((tobool4.i$1_0 (distinct _$1_3 0)))
                                 (=>
                                    tobool4.i$1_0
                                    (let
                                       ((incdec.ptr.i$1_0 (+ t.addr.i.0$1_0 1)))
                                       (let
                                          ((t.addr.i.0$1_0 incdec.ptr.i$1_0))
                                          (=>
                                             (let
                                                ((_$2_1 _$2_1_old)
                                                 (count.0$2_0 count.0$2_0_old)
                                                 (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                 (reject$2_0 reject$2_0_old)
                                                 (t.0$2_0 t.0$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (tobool2$2_0 (distinct 1 0)))
                                                (=>
                                                   tobool2$2_0
                                                   (let
                                                      ((_$2_2 (select HEAP$2 t.0$2_0)))
                                                      (let
                                                         ((conv3$2_0 _$2_2)
                                                          (conv4$2_0 _$2_1))
                                                         (let
                                                            ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                                            (=>
                                                               (not cmp$2_0)
                                                               (let
                                                                  ((_$2_3 (select HEAP$2 t.0$2_0)))
                                                                  (let
                                                                     ((tobool6$2_0 (distinct _$2_3 0)))
                                                                     (=>
                                                                        tobool6$2_0
                                                                        (let
                                                                           ((incdec.ptr9$2_0 (+ t.0$2_0 1)))
                                                                           (let
                                                                              ((t.0$2_0 incdec.ptr9$2_0))
                                                                              false)))))))))))
                                             (INV_MAIN_0 conv.i$1_0 count.0$1_0 incdec.ptr$1_0 reject$1_0 t.addr.i.0$1_0 HEAP$1 _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((_$2_1 _$2_1_old)
             (count.0$2_0 count.0$2_0_old)
             (incdec.ptr$2_0 incdec.ptr$2_0_old)
             (reject$2_0 reject$2_0_old)
             (t.0$2_0 t.0$2_0_old)
             (HEAP$2 HEAP$2_old)
             (tobool2$2_0 (distinct 1 0)))
            (=>
               tobool2$2_0
               (let
                  ((_$2_2 (select HEAP$2 t.0$2_0)))
                  (let
                     ((conv3$2_0 _$2_2)
                      (conv4$2_0 _$2_1))
                     (let
                        ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((_$2_3 (select HEAP$2 t.0$2_0)))
                              (let
                                 ((tobool6$2_0 (distinct _$2_3 0)))
                                 (=>
                                    tobool6$2_0
                                    (let
                                       ((incdec.ptr9$2_0 (+ t.0$2_0 1)))
                                       (let
                                          ((t.0$2_0 incdec.ptr9$2_0))
                                          (=>
                                             (let
                                                ((conv.i$1_0 conv.i$1_0_old)
                                                 (count.0$1_0 count.0$1_0_old)
                                                 (incdec.ptr$1_0 incdec.ptr$1_0_old)
                                                 (reject$1_0 reject$1_0_old)
                                                 (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
                                                 (HEAP$1 HEAP$1_old)
                                                 (tobool.i$1_0 (distinct 1 0)))
                                                (=>
                                                   tobool.i$1_0
                                                   (let
                                                      ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                                                      (let
                                                         ((conv1.i$1_0 _$1_2)
                                                          (conv2.i$1_0 conv.i$1_0))
                                                         (let
                                                            ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                                                            (=>
                                                               (not cmp.i$1_0)
                                                               (let
                                                                  ((_$1_3 (select HEAP$1 t.addr.i.0$1_0)))
                                                                  (let
                                                                     ((tobool4.i$1_0 (distinct _$1_3 0)))
                                                                     (=>
                                                                        tobool4.i$1_0
                                                                        (let
                                                                           ((incdec.ptr.i$1_0 (+ t.addr.i.0$1_0 1)))
                                                                           (let
                                                                              ((t.addr.i.0$1_0 incdec.ptr.i$1_0))
                                                                              false)))))))))))
                                             (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1 count.0$2_0 incdec.ptr$2_0 reject$2_0 t.0$2_0 HEAP$2))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           cmp.i$1_0
                           (let
                              ((retval.i.0$1_0 t.addr.i.0$1_0))
                              (let
                                 ((cmp$1_0 (= retval.i.0$1_0 0)))
                                 (=>
                                    cmp$1_0
                                    (let
                                       ((inc$1_0 (+ count.0$1_0 1)))
                                       (let
                                          ((s.addr.0$1_0 incdec.ptr$1_0)
                                           (count.0$1_0 inc$1_0)
                                           (_$2_1 _$2_1_old)
                                           (count.0$2_0 count.0$2_0_old)
                                           (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                           (reject$2_0 reject$2_0_old)
                                           (t.0$2_0 t.0$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (tobool2$2_0 (distinct 1 0)))
                                          (=>
                                             tobool2$2_0
                                             (let
                                                ((_$2_2 (select HEAP$2 t.0$2_0)))
                                                (let
                                                   ((conv3$2_0 _$2_2)
                                                    (conv4$2_0 _$2_1))
                                                   (let
                                                      ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                                      (=>
                                                         (not cmp$2_0)
                                                         (let
                                                            ((_$2_3 (select HEAP$2 t.0$2_0)))
                                                            (let
                                                               ((tobool6$2_0 (distinct _$2_3 0)))
                                                               (=>
                                                                  (not tobool6$2_0)
                                                                  (let
                                                                     ((inc$2_0 (+ count.0$2_0 1)))
                                                                     (let
                                                                        ((count.0$2_0 inc$2_0)
                                                                         (s.addr.0$2_0 incdec.ptr$2_0))
                                                                        (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 HEAP$1 count.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           cmp.i$1_0
                           (let
                              ((retval.i.0$1_0 t.addr.i.0$1_0))
                              (let
                                 ((cmp$1_0 (= retval.i.0$1_0 0)))
                                 (=>
                                    cmp$1_0
                                    (let
                                       ((inc$1_0 (+ count.0$1_0 1)))
                                       (let
                                          ((s.addr.0$1_0 incdec.ptr$1_0)
                                           (count.0$1_0 inc$1_0)
                                           (_$2_1 _$2_1_old)
                                           (count.0$2_0 count.0$2_0_old)
                                           (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                           (reject$2_0 reject$2_0_old)
                                           (t.0$2_0 t.0$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (tobool2$2_0 (distinct 1 0)))
                                          (=>
                                             (not tobool2$2_0)
                                             (let
                                                ((count.0$2_0 count.0$2_0)
                                                 (s.addr.0$2_0 incdec.ptr$2_0))
                                                (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 HEAP$1 count.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2)))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           (not cmp.i$1_0)
                           (let
                              ((_$1_3 (select HEAP$1 t.addr.i.0$1_0)))
                              (let
                                 ((tobool4.i$1_0 (distinct _$1_3 0)))
                                 (=>
                                    (not tobool4.i$1_0)
                                    (let
                                       ((retval.i.0$1_0 0))
                                       (let
                                          ((cmp$1_0 (= retval.i.0$1_0 0)))
                                          (=>
                                             cmp$1_0
                                             (let
                                                ((inc$1_0 (+ count.0$1_0 1)))
                                                (let
                                                   ((s.addr.0$1_0 incdec.ptr$1_0)
                                                    (count.0$1_0 inc$1_0)
                                                    (_$2_1 _$2_1_old)
                                                    (count.0$2_0 count.0$2_0_old)
                                                    (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                    (reject$2_0 reject$2_0_old)
                                                    (t.0$2_0 t.0$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (tobool2$2_0 (distinct 1 0)))
                                                   (=>
                                                      tobool2$2_0
                                                      (let
                                                         ((_$2_2 (select HEAP$2 t.0$2_0)))
                                                         (let
                                                            ((conv3$2_0 _$2_2)
                                                             (conv4$2_0 _$2_1))
                                                            (let
                                                               ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                                               (=>
                                                                  (not cmp$2_0)
                                                                  (let
                                                                     ((_$2_3 (select HEAP$2 t.0$2_0)))
                                                                     (let
                                                                        ((tobool6$2_0 (distinct _$2_3 0)))
                                                                        (=>
                                                                           (not tobool6$2_0)
                                                                           (let
                                                                              ((inc$2_0 (+ count.0$2_0 1)))
                                                                              (let
                                                                                 ((count.0$2_0 inc$2_0)
                                                                                  (s.addr.0$2_0 incdec.ptr$2_0))
                                                                                 (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 HEAP$1 count.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2))))))))))))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               tobool.i$1_0
               (let
                  ((_$1_2 (select HEAP$1 t.addr.i.0$1_0)))
                  (let
                     ((conv1.i$1_0 _$1_2)
                      (conv2.i$1_0 conv.i$1_0))
                     (let
                        ((cmp.i$1_0 (= conv1.i$1_0 conv2.i$1_0)))
                        (=>
                           (not cmp.i$1_0)
                           (let
                              ((_$1_3 (select HEAP$1 t.addr.i.0$1_0)))
                              (let
                                 ((tobool4.i$1_0 (distinct _$1_3 0)))
                                 (=>
                                    (not tobool4.i$1_0)
                                    (let
                                       ((retval.i.0$1_0 0))
                                       (let
                                          ((cmp$1_0 (= retval.i.0$1_0 0)))
                                          (=>
                                             cmp$1_0
                                             (let
                                                ((inc$1_0 (+ count.0$1_0 1)))
                                                (let
                                                   ((s.addr.0$1_0 incdec.ptr$1_0)
                                                    (count.0$1_0 inc$1_0)
                                                    (_$2_1 _$2_1_old)
                                                    (count.0$2_0 count.0$2_0_old)
                                                    (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                    (reject$2_0 reject$2_0_old)
                                                    (t.0$2_0 t.0$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (tobool2$2_0 (distinct 1 0)))
                                                   (=>
                                                      (not tobool2$2_0)
                                                      (let
                                                         ((count.0$2_0 count.0$2_0)
                                                          (s.addr.0$2_0 incdec.ptr$2_0))
                                                         (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 HEAP$1 count.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2))))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               (not tobool.i$1_0)
               (let
                  ((retval.i.0$1_0 t.addr.i.0$1_0))
                  (let
                     ((cmp$1_0 (= retval.i.0$1_0 0)))
                     (=>
                        cmp$1_0
                        (let
                           ((inc$1_0 (+ count.0$1_0 1)))
                           (let
                              ((s.addr.0$1_0 incdec.ptr$1_0)
                               (count.0$1_0 inc$1_0)
                               (_$2_1 _$2_1_old)
                               (count.0$2_0 count.0$2_0_old)
                               (incdec.ptr$2_0 incdec.ptr$2_0_old)
                               (reject$2_0 reject$2_0_old)
                               (t.0$2_0 t.0$2_0_old)
                               (HEAP$2 HEAP$2_old)
                               (tobool2$2_0 (distinct 1 0)))
                              (=>
                                 tobool2$2_0
                                 (let
                                    ((_$2_2 (select HEAP$2 t.0$2_0)))
                                    (let
                                       ((conv3$2_0 _$2_2)
                                        (conv4$2_0 _$2_1))
                                       (let
                                          ((cmp$2_0 (= conv3$2_0 conv4$2_0)))
                                          (=>
                                             (not cmp$2_0)
                                             (let
                                                ((_$2_3 (select HEAP$2 t.0$2_0)))
                                                (let
                                                   ((tobool6$2_0 (distinct _$2_3 0)))
                                                   (=>
                                                      (not tobool6$2_0)
                                                      (let
                                                         ((inc$2_0 (+ count.0$2_0 1)))
                                                         (let
                                                            ((count.0$2_0 inc$2_0)
                                                             (s.addr.0$2_0 incdec.ptr$2_0))
                                                            (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 HEAP$1 count.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2)))))))))))))))))))))
(assert
   (forall
      ((conv.i$1_0_old Int)
       (count.0$1_0_old Int)
       (incdec.ptr$1_0_old Int)
       (reject$1_0_old Int)
       (t.addr.i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 conv.i$1_0_old count.0$1_0_old incdec.ptr$1_0_old reject$1_0_old t.addr.i.0$1_0_old HEAP$1_old _$2_1_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.0$2_0_old HEAP$2_old)
         (let
            ((conv.i$1_0 conv.i$1_0_old)
             (count.0$1_0 count.0$1_0_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (reject$1_0 reject$1_0_old)
             (t.addr.i.0$1_0 t.addr.i.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool.i$1_0 (distinct 1 0)))
            (=>
               (not tobool.i$1_0)
               (let
                  ((retval.i.0$1_0 t.addr.i.0$1_0))
                  (let
                     ((cmp$1_0 (= retval.i.0$1_0 0)))
                     (=>
                        cmp$1_0
                        (let
                           ((inc$1_0 (+ count.0$1_0 1)))
                           (let
                              ((s.addr.0$1_0 incdec.ptr$1_0)
                               (count.0$1_0 inc$1_0)
                               (_$2_1 _$2_1_old)
                               (count.0$2_0 count.0$2_0_old)
                               (incdec.ptr$2_0 incdec.ptr$2_0_old)
                               (reject$2_0 reject$2_0_old)
                               (t.0$2_0 t.0$2_0_old)
                               (HEAP$2 HEAP$2_old)
                               (tobool2$2_0 (distinct 1 0)))
                              (=>
                                 (not tobool2$2_0)
                                 (let
                                    ((count.0$2_0 count.0$2_0)
                                     (s.addr.0$2_0 incdec.ptr$2_0))
                                    (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 HEAP$1 count.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2)))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (count.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old HEAP$1_old count.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((count.0$1_0 count.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        (not tobool$1_0)
                        (let
                           ((result$1 count.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (count.0$2_0 count.0$2_0_old)
                            (reject$2_0 reject$2_0_old)
                            (s.addr.0$2_0 s.addr.0$2_0_old)
                            (HEAP$2 HEAP$2_old))
                           (let
                              ((_$2_0 (select HEAP$2 s.addr.0$2_0)))
                              (let
                                 ((conv$2_0 _$2_0))
                                 (let
                                    ((tobool$2_0 (distinct conv$2_0 0)))
                                    (=>
                                       tobool$2_0
                                       (let
                                          ((incdec.ptr$2_0 (+ s.addr.0$2_0 1))
                                           (_$2_1 (select HEAP$2 s.addr.0$2_0))
                                           (t.0$2_0 reject$2_0))
                                          false))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (count.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old HEAP$1_old count.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((count.0$1_0 count.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        tobool$1_0
                        (let
                           ((incdec.ptr$1_0 (+ s.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((conv.i$1_0 conv1$1_0)
                                  (t.addr.i.0$1_0 reject$1_0)
                                  (count.0$2_0 count.0$2_0_old)
                                  (reject$2_0 reject$2_0_old)
                                  (s.addr.0$2_0 s.addr.0$2_0_old)
                                  (HEAP$2 HEAP$2_old))
                                 (let
                                    ((_$2_0 (select HEAP$2 s.addr.0$2_0)))
                                    (let
                                       ((conv$2_0 _$2_0))
                                       (let
                                          ((tobool$2_0 (distinct conv$2_0 0)))
                                          (=>
                                             (not tobool$2_0)
                                             (let
                                                ((result$2 count.0$2_0)
                                                 (HEAP$2_res HEAP$2))
                                                false))))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (count.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old HEAP$1_old count.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((count.0$1_0 count.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        (not tobool$1_0)
                        (let
                           ((result$1 count.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (count.0$2_0 count.0$2_0_old)
                            (reject$2_0 reject$2_0_old)
                            (s.addr.0$2_0 s.addr.0$2_0_old)
                            (HEAP$2 HEAP$2_old))
                           (let
                              ((_$2_0 (select HEAP$2 s.addr.0$2_0)))
                              (let
                                 ((conv$2_0 _$2_0))
                                 (let
                                    ((tobool$2_0 (distinct conv$2_0 0)))
                                    (=>
                                       (not tobool$2_0)
                                       (let
                                          ((result$2 count.0$2_0)
                                           (HEAP$2_res HEAP$2))
                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (count.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old HEAP$1_old count.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((count.0$1_0 count.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        tobool$1_0
                        (let
                           ((incdec.ptr$1_0 (+ s.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((conv.i$1_0 conv1$1_0)
                                  (t.addr.i.0$1_0 reject$1_0)
                                  (count.0$2_0 count.0$2_0_old)
                                  (reject$2_0 reject$2_0_old)
                                  (s.addr.0$2_0 s.addr.0$2_0_old)
                                  (HEAP$2 HEAP$2_old))
                                 (let
                                    ((_$2_0 (select HEAP$2 s.addr.0$2_0)))
                                    (let
                                       ((conv$2_0 _$2_0))
                                       (let
                                          ((tobool$2_0 (distinct conv$2_0 0)))
                                          (=>
                                             tobool$2_0
                                             (let
                                                ((incdec.ptr$2_0 (+ s.addr.0$2_0 1))
                                                 (_$2_1 (select HEAP$2 s.addr.0$2_0))
                                                 (t.0$2_0 reject$2_0))
                                                (INV_MAIN_0 conv.i$1_0 count.0$1_0 incdec.ptr$1_0 reject$1_0 t.addr.i.0$1_0 HEAP$1 _$2_1 count.0$2_0 incdec.ptr$2_0 reject$2_0 t.0$2_0 HEAP$2)))))))))))))))))
(check-sat)
(get-model)
