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
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))))
; :annot (INV_MAIN_0 count.0$1_0 i.0$1_0 reject$1_0 s.addr.0$1_0 HEAP$1 conv.i$2_0 count.0$2_0 incdec.ptr$2_0 reject$2_0 t.addr.i.0$2_0 HEAP$2)
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
    Int
    Int)
   Bool)
; :annot (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 HEAP$1 count.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_1
   (Int
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
                (count.0$1_0 0)
                (s.addr.0$1_0 s$1_0)
                (s$2_0 s$2_0_old))
               (let
                  ((reject$2_0 reject$2_0_old)
                   (HEAP$2 HEAP$2_old)
                   (s.addr.0$2_0 s$2_0)
                   (count.0$2_0 0))
                  (forall
                     ((i1 Int)
                      (i2 Int))
                     (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 i1 (select HEAP$1 i1) count.0$2_0 reject$2_0 s.addr.0$2_0 i2 (select HEAP$2 i2)))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (i.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv.i$2_0_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.addr.i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 count.0$1_0_old i.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv.i$2_0_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.addr.i.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((count.0$1_0 count.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((reject$1_0 reject$1_0_old)
                (s.addr.0$1_0 s.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc$1_0 (+ i.0$1_0 1)))
               (let
                  ((i.0$1_0 inc$1_0))
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                        (let
                           ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((tobool2$1_0 (distinct _$1_1 0)))
                              (=>
                                 tobool2$1_0
                                 (let
                                    ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                    (let
                                       ((conv4$1_0 _$1_2)
                                        (idxprom5$1_0 i.0$1_0))
                                       (let
                                          ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                          (let
                                             ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                             (let
                                                ((conv7$1_0 _$1_3))
                                                (let
                                                   ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                   (=>
                                                      cmp$1_0
                                                      (let
                                                         ((result$1 count.0$1_0)
                                                          (HEAP$1_res HEAP$1)
                                                          (conv.i$2_0 conv.i$2_0_old)
                                                          (count.0$2_0 count.0$2_0_old)
                                                          (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                          (reject$2_0 reject$2_0_old)
                                                          (t.addr.i.0$2_0 t.addr.i.0$2_0_old))
                                                         (let
                                                            ((HEAP$2 HEAP$2_old)
                                                             (incdec.ptr.i$2_0 (+ t.addr.i.0$2_0 1)))
                                                            (let
                                                               ((t.addr.i.0$2_0 incdec.ptr.i$2_0))
                                                               (let
                                                                  ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                  (let
                                                                     ((conv1.i$2_0 _$2_2)
                                                                      (conv2.i$2_0 conv.i$2_0))
                                                                     (let
                                                                        ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                        (=>
                                                                           cmp.i$2_0
                                                                           (let
                                                                              ((retval.i.0$2_0 t.addr.i.0$2_0))
                                                                              (let
                                                                                 ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                                 (=>
                                                                                    cmp$2_0
                                                                                    (let
                                                                                       ((inc$2_0 (+ count.0$2_0 1)))
                                                                                       (let
                                                                                          ((s.addr.0$2_0 incdec.ptr$2_0)
                                                                                           (count.0$2_0 inc$2_0))
                                                                                          false))))))))))))))))))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (i.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv.i$2_0_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.addr.i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 count.0$1_0_old i.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv.i$2_0_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.addr.i.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((count.0$1_0 count.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((reject$1_0 reject$1_0_old)
                (s.addr.0$1_0 s.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc$1_0 (+ i.0$1_0 1)))
               (let
                  ((i.0$1_0 inc$1_0))
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                        (let
                           ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((tobool2$1_0 (distinct _$1_1 0)))
                              (=>
                                 tobool2$1_0
                                 (let
                                    ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                    (let
                                       ((conv4$1_0 _$1_2)
                                        (idxprom5$1_0 i.0$1_0))
                                       (let
                                          ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                          (let
                                             ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                             (let
                                                ((conv7$1_0 _$1_3))
                                                (let
                                                   ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                   (=>
                                                      cmp$1_0
                                                      (let
                                                         ((result$1 count.0$1_0)
                                                          (HEAP$1_res HEAP$1)
                                                          (conv.i$2_0 conv.i$2_0_old)
                                                          (count.0$2_0 count.0$2_0_old)
                                                          (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                          (reject$2_0 reject$2_0_old)
                                                          (t.addr.i.0$2_0 t.addr.i.0$2_0_old))
                                                         (let
                                                            ((HEAP$2 HEAP$2_old)
                                                             (incdec.ptr.i$2_0 (+ t.addr.i.0$2_0 1)))
                                                            (let
                                                               ((t.addr.i.0$2_0 incdec.ptr.i$2_0))
                                                               (let
                                                                  ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                  (let
                                                                     ((conv1.i$2_0 _$2_2)
                                                                      (conv2.i$2_0 conv.i$2_0))
                                                                     (let
                                                                        ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                        (=>
                                                                           (not cmp.i$2_0)
                                                                           (let
                                                                              ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                                              (let
                                                                                 ((tobool.i$2_0 (distinct _$2_3 0)))
                                                                                 (=>
                                                                                    (not tobool.i$2_0)
                                                                                    (let
                                                                                       ((retval.i.0$2_0 0))
                                                                                       (let
                                                                                          ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                                          (=>
                                                                                             cmp$2_0
                                                                                             (let
                                                                                                ((inc$2_0 (+ count.0$2_0 1)))
                                                                                                (let
                                                                                                   ((s.addr.0$2_0 incdec.ptr$2_0)
                                                                                                    (count.0$2_0 inc$2_0))
                                                                                                   false)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (i.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv.i$2_0_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.addr.i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 count.0$1_0_old i.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv.i$2_0_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.addr.i.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((count.0$1_0 count.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((reject$1_0 reject$1_0_old)
                (s.addr.0$1_0 s.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc$1_0 (+ i.0$1_0 1)))
               (let
                  ((i.0$1_0 inc$1_0))
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                        (let
                           ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((tobool2$1_0 (distinct _$1_1 0)))
                              (=>
                                 (not tobool2$1_0)
                                 (let
                                    ((inc10$1_0 (+ count.0$1_0 1))
                                     (incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                    (let
                                       ((count.0$1_0 inc10$1_0)
                                        (s.addr.0$1_0 incdec.ptr$1_0)
                                        (conv.i$2_0 conv.i$2_0_old)
                                        (count.0$2_0 count.0$2_0_old)
                                        (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                        (reject$2_0 reject$2_0_old)
                                        (t.addr.i.0$2_0 t.addr.i.0$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (incdec.ptr.i$2_0 (+ t.addr.i.0$2_0 1)))
                                          (let
                                             ((t.addr.i.0$2_0 incdec.ptr.i$2_0))
                                             (let
                                                ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                (let
                                                   ((conv1.i$2_0 _$2_2)
                                                    (conv2.i$2_0 conv.i$2_0))
                                                   (let
                                                      ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                      (=>
                                                         cmp.i$2_0
                                                         (let
                                                            ((retval.i.0$2_0 t.addr.i.0$2_0))
                                                            (let
                                                               ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                               (=>
                                                                  (not cmp$2_0)
                                                                  (let
                                                                     ((result$2 count.0$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     false)))))))))))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (i.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv.i$2_0_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.addr.i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 count.0$1_0_old i.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv.i$2_0_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.addr.i.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((count.0$1_0 count.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((reject$1_0 reject$1_0_old)
                (s.addr.0$1_0 s.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc$1_0 (+ i.0$1_0 1)))
               (let
                  ((i.0$1_0 inc$1_0))
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                        (let
                           ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((tobool2$1_0 (distinct _$1_1 0)))
                              (=>
                                 (not tobool2$1_0)
                                 (let
                                    ((inc10$1_0 (+ count.0$1_0 1))
                                     (incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                    (let
                                       ((count.0$1_0 inc10$1_0)
                                        (s.addr.0$1_0 incdec.ptr$1_0)
                                        (conv.i$2_0 conv.i$2_0_old)
                                        (count.0$2_0 count.0$2_0_old)
                                        (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                        (reject$2_0 reject$2_0_old)
                                        (t.addr.i.0$2_0 t.addr.i.0$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (incdec.ptr.i$2_0 (+ t.addr.i.0$2_0 1)))
                                          (let
                                             ((t.addr.i.0$2_0 incdec.ptr.i$2_0))
                                             (let
                                                ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                (let
                                                   ((conv1.i$2_0 _$2_2)
                                                    (conv2.i$2_0 conv.i$2_0))
                                                   (let
                                                      ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                      (=>
                                                         (not cmp.i$2_0)
                                                         (let
                                                            ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                            (let
                                                               ((tobool.i$2_0 (distinct _$2_3 0)))
                                                               (=>
                                                                  (not tobool.i$2_0)
                                                                  (let
                                                                     ((retval.i.0$2_0 0))
                                                                     (let
                                                                        ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                        (=>
                                                                           (not cmp$2_0)
                                                                           (let
                                                                              ((result$2 count.0$2_0)
                                                                               (HEAP$2_res HEAP$2))
                                                                              false))))))))))))))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (i.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv.i$2_0_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.addr.i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 count.0$1_0_old i.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv.i$2_0_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.addr.i.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((count.0$1_0 count.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((reject$1_0 reject$1_0_old)
                (s.addr.0$1_0 s.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc$1_0 (+ i.0$1_0 1)))
               (let
                  ((i.0$1_0 inc$1_0))
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                        (let
                           ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((tobool2$1_0 (distinct _$1_1 0)))
                              (=>
                                 tobool2$1_0
                                 (let
                                    ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                    (let
                                       ((conv4$1_0 _$1_2)
                                        (idxprom5$1_0 i.0$1_0))
                                       (let
                                          ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                          (let
                                             ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                             (let
                                                ((conv7$1_0 _$1_3))
                                                (let
                                                   ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                   (=>
                                                      cmp$1_0
                                                      (let
                                                         ((result$1 count.0$1_0)
                                                          (HEAP$1_res HEAP$1)
                                                          (conv.i$2_0 conv.i$2_0_old)
                                                          (count.0$2_0 count.0$2_0_old)
                                                          (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                          (reject$2_0 reject$2_0_old)
                                                          (t.addr.i.0$2_0 t.addr.i.0$2_0_old))
                                                         (let
                                                            ((HEAP$2 HEAP$2_old)
                                                             (incdec.ptr.i$2_0 (+ t.addr.i.0$2_0 1)))
                                                            (let
                                                               ((t.addr.i.0$2_0 incdec.ptr.i$2_0))
                                                               (let
                                                                  ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                  (let
                                                                     ((conv1.i$2_0 _$2_2)
                                                                      (conv2.i$2_0 conv.i$2_0))
                                                                     (let
                                                                        ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                        (=>
                                                                           cmp.i$2_0
                                                                           (let
                                                                              ((retval.i.0$2_0 t.addr.i.0$2_0))
                                                                              (let
                                                                                 ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                                 (=>
                                                                                    (not cmp$2_0)
                                                                                    (let
                                                                                       ((result$2 count.0$2_0)
                                                                                        (HEAP$2_res HEAP$2))
                                                                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (i.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv.i$2_0_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.addr.i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 count.0$1_0_old i.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv.i$2_0_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.addr.i.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((count.0$1_0 count.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((reject$1_0 reject$1_0_old)
                (s.addr.0$1_0 s.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc$1_0 (+ i.0$1_0 1)))
               (let
                  ((i.0$1_0 inc$1_0))
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                        (let
                           ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((tobool2$1_0 (distinct _$1_1 0)))
                              (=>
                                 tobool2$1_0
                                 (let
                                    ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                    (let
                                       ((conv4$1_0 _$1_2)
                                        (idxprom5$1_0 i.0$1_0))
                                       (let
                                          ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                          (let
                                             ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                             (let
                                                ((conv7$1_0 _$1_3))
                                                (let
                                                   ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                   (=>
                                                      cmp$1_0
                                                      (let
                                                         ((result$1 count.0$1_0)
                                                          (HEAP$1_res HEAP$1)
                                                          (conv.i$2_0 conv.i$2_0_old)
                                                          (count.0$2_0 count.0$2_0_old)
                                                          (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                          (reject$2_0 reject$2_0_old)
                                                          (t.addr.i.0$2_0 t.addr.i.0$2_0_old))
                                                         (let
                                                            ((HEAP$2 HEAP$2_old)
                                                             (incdec.ptr.i$2_0 (+ t.addr.i.0$2_0 1)))
                                                            (let
                                                               ((t.addr.i.0$2_0 incdec.ptr.i$2_0))
                                                               (let
                                                                  ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                  (let
                                                                     ((conv1.i$2_0 _$2_2)
                                                                      (conv2.i$2_0 conv.i$2_0))
                                                                     (let
                                                                        ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                        (=>
                                                                           (not cmp.i$2_0)
                                                                           (let
                                                                              ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                                              (let
                                                                                 ((tobool.i$2_0 (distinct _$2_3 0)))
                                                                                 (=>
                                                                                    (not tobool.i$2_0)
                                                                                    (let
                                                                                       ((retval.i.0$2_0 0))
                                                                                       (let
                                                                                          ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                                          (=>
                                                                                             (not cmp$2_0)
                                                                                             (let
                                                                                                ((result$2 count.0$2_0)
                                                                                                 (HEAP$2_res HEAP$2))
                                                                                                (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (i.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv.i$2_0_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.addr.i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 count.0$1_0_old i.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv.i$2_0_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.addr.i.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((count.0$1_0 count.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((reject$1_0 reject$1_0_old)
                (s.addr.0$1_0 s.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc$1_0 (+ i.0$1_0 1)))
               (let
                  ((i.0$1_0 inc$1_0))
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                        (let
                           ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((tobool2$1_0 (distinct _$1_1 0)))
                              (=>
                                 tobool2$1_0
                                 (let
                                    ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                    (let
                                       ((conv4$1_0 _$1_2)
                                        (idxprom5$1_0 i.0$1_0))
                                       (let
                                          ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                          (let
                                             ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                             (let
                                                ((conv7$1_0 _$1_3))
                                                (let
                                                   ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                   (=>
                                                      (not cmp$1_0)
                                                      (let
                                                         ((conv.i$2_0 conv.i$2_0_old)
                                                          (count.0$2_0 count.0$2_0_old)
                                                          (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                          (reject$2_0 reject$2_0_old)
                                                          (t.addr.i.0$2_0 t.addr.i.0$2_0_old))
                                                         (let
                                                            ((HEAP$2 HEAP$2_old)
                                                             (incdec.ptr.i$2_0 (+ t.addr.i.0$2_0 1)))
                                                            (let
                                                               ((t.addr.i.0$2_0 incdec.ptr.i$2_0))
                                                               (let
                                                                  ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                  (let
                                                                     ((conv1.i$2_0 _$2_2)
                                                                      (conv2.i$2_0 conv.i$2_0))
                                                                     (let
                                                                        ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                        (=>
                                                                           (not cmp.i$2_0)
                                                                           (let
                                                                              ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                                              (let
                                                                                 ((tobool.i$2_0 (distinct _$2_3 0)))
                                                                                 (=>
                                                                                    tobool.i$2_0
                                                                                    (forall
                                                                                       ((i1 Int)
                                                                                        (i2 Int))
                                                                                       (INV_MAIN_0 count.0$1_0 i.0$1_0 reject$1_0 s.addr.0$1_0 i1 (select HEAP$1 i1) conv.i$2_0 count.0$2_0 incdec.ptr$2_0 reject$2_0 t.addr.i.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (i.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv.i$2_0_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.addr.i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 count.0$1_0_old i.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv.i$2_0_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.addr.i.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((count.0$1_0 count.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((reject$1_0 reject$1_0_old)
                (s.addr.0$1_0 s.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc$1_0 (+ i.0$1_0 1)))
               (let
                  ((i.0$1_0 inc$1_0))
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                        (let
                           ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((tobool2$1_0 (distinct _$1_1 0)))
                              (=>
                                 tobool2$1_0
                                 (let
                                    ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                    (let
                                       ((conv4$1_0 _$1_2)
                                        (idxprom5$1_0 i.0$1_0))
                                       (let
                                          ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                          (let
                                             ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                             (let
                                                ((conv7$1_0 _$1_3))
                                                (let
                                                   ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                   (=>
                                                      (not cmp$1_0)
                                                      (=>
                                                         (let
                                                            ((conv.i$2_0 conv.i$2_0_old)
                                                             (count.0$2_0 count.0$2_0_old)
                                                             (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                             (reject$2_0 reject$2_0_old)
                                                             (t.addr.i.0$2_0 t.addr.i.0$2_0_old))
                                                            (let
                                                               ((HEAP$2 HEAP$2_old)
                                                                (incdec.ptr.i$2_0 (+ t.addr.i.0$2_0 1)))
                                                               (let
                                                                  ((t.addr.i.0$2_0 incdec.ptr.i$2_0))
                                                                  (let
                                                                     ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                     (let
                                                                        ((conv1.i$2_0 _$2_2)
                                                                         (conv2.i$2_0 conv.i$2_0))
                                                                        (let
                                                                           ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                           (=>
                                                                              (not cmp.i$2_0)
                                                                              (let
                                                                                 ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                 (let
                                                                                    ((tobool.i$2_0 (distinct _$2_3 0)))
                                                                                    (not tobool.i$2_0))))))))))
                                                         (forall
                                                            ((i1 Int)
                                                             (i2_old Int))
                                                            (INV_MAIN_0 count.0$1_0 i.0$1_0 reject$1_0 s.addr.0$1_0 i1 (select HEAP$1 i1) conv.i$2_0_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.addr.i.0$2_0_old i2_old (select HEAP$2_old i2_old))))))))))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (i.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv.i$2_0_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.addr.i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 count.0$1_0_old i.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv.i$2_0_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.addr.i.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv.i$2_0 conv.i$2_0_old)
             (count.0$2_0 count.0$2_0_old)
             (incdec.ptr$2_0 incdec.ptr$2_0_old)
             (reject$2_0 reject$2_0_old)
             (t.addr.i.0$2_0 t.addr.i.0$2_0_old))
            (let
               ((HEAP$2 HEAP$2_old)
                (incdec.ptr.i$2_0 (+ t.addr.i.0$2_0 1)))
               (let
                  ((t.addr.i.0$2_0 incdec.ptr.i$2_0))
                  (let
                     ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                     (let
                        ((conv1.i$2_0 _$2_2)
                         (conv2.i$2_0 conv.i$2_0))
                        (let
                           ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                           (=>
                              (not cmp.i$2_0)
                              (let
                                 ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                 (let
                                    ((tobool.i$2_0 (distinct _$2_3 0)))
                                    (=>
                                       tobool.i$2_0
                                       (=>
                                          (let
                                             ((count.0$1_0 count.0$1_0_old)
                                              (i.0$1_0 i.0$1_0_old))
                                             (let
                                                ((reject$1_0 reject$1_0_old)
                                                 (s.addr.0$1_0 s.addr.0$1_0_old)
                                                 (HEAP$1 HEAP$1_old)
                                                 (inc$1_0 (+ i.0$1_0 1)))
                                                (let
                                                   ((i.0$1_0 inc$1_0))
                                                   (let
                                                      ((idxprom$1_0 i.0$1_0))
                                                      (let
                                                         ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                                         (let
                                                            ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                                            (let
                                                               ((tobool2$1_0 (distinct _$1_1 0)))
                                                               (=>
                                                                  tobool2$1_0
                                                                  (let
                                                                     ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                                                     (let
                                                                        ((conv4$1_0 _$1_2)
                                                                         (idxprom5$1_0 i.0$1_0))
                                                                        (let
                                                                           ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                                                           (let
                                                                              ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                                                              (let
                                                                                 ((conv7$1_0 _$1_3))
                                                                                 (let
                                                                                    ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                                                    (not (not cmp$1_0))))))))))))))))
                                          (forall
                                             ((i1_old Int)
                                              (i2 Int))
                                             (INV_MAIN_0 count.0$1_0_old i.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv.i$2_0 count.0$2_0 incdec.ptr$2_0 reject$2_0 t.addr.i.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (i.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv.i$2_0_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.addr.i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 count.0$1_0_old i.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv.i$2_0_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.addr.i.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((count.0$1_0 count.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((reject$1_0 reject$1_0_old)
                (s.addr.0$1_0 s.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc$1_0 (+ i.0$1_0 1)))
               (let
                  ((i.0$1_0 inc$1_0))
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                        (let
                           ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((tobool2$1_0 (distinct _$1_1 0)))
                              (=>
                                 (not tobool2$1_0)
                                 (let
                                    ((inc10$1_0 (+ count.0$1_0 1))
                                     (incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                    (let
                                       ((count.0$1_0 inc10$1_0)
                                        (s.addr.0$1_0 incdec.ptr$1_0)
                                        (conv.i$2_0 conv.i$2_0_old)
                                        (count.0$2_0 count.0$2_0_old)
                                        (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                        (reject$2_0 reject$2_0_old)
                                        (t.addr.i.0$2_0 t.addr.i.0$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (incdec.ptr.i$2_0 (+ t.addr.i.0$2_0 1)))
                                          (let
                                             ((t.addr.i.0$2_0 incdec.ptr.i$2_0))
                                             (let
                                                ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                (let
                                                   ((conv1.i$2_0 _$2_2)
                                                    (conv2.i$2_0 conv.i$2_0))
                                                   (let
                                                      ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                      (=>
                                                         cmp.i$2_0
                                                         (let
                                                            ((retval.i.0$2_0 t.addr.i.0$2_0))
                                                            (let
                                                               ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                               (=>
                                                                  cmp$2_0
                                                                  (let
                                                                     ((inc$2_0 (+ count.0$2_0 1)))
                                                                     (let
                                                                        ((s.addr.0$2_0 incdec.ptr$2_0)
                                                                         (count.0$2_0 inc$2_0))
                                                                        (forall
                                                                           ((i1 Int)
                                                                            (i2 Int))
                                                                           (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 i1 (select HEAP$1 i1) count.0$2_0 reject$2_0 s.addr.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))
(assert
   (forall
      ((count.0$1_0_old Int)
       (i.0$1_0_old Int)
       (reject$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv.i$2_0_old Int)
       (count.0$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (reject$2_0_old Int)
       (t.addr.i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 count.0$1_0_old i.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv.i$2_0_old count.0$2_0_old incdec.ptr$2_0_old reject$2_0_old t.addr.i.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((count.0$1_0 count.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((reject$1_0 reject$1_0_old)
                (s.addr.0$1_0 s.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc$1_0 (+ i.0$1_0 1)))
               (let
                  ((i.0$1_0 inc$1_0))
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                        (let
                           ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((tobool2$1_0 (distinct _$1_1 0)))
                              (=>
                                 (not tobool2$1_0)
                                 (let
                                    ((inc10$1_0 (+ count.0$1_0 1))
                                     (incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                    (let
                                       ((count.0$1_0 inc10$1_0)
                                        (s.addr.0$1_0 incdec.ptr$1_0)
                                        (conv.i$2_0 conv.i$2_0_old)
                                        (count.0$2_0 count.0$2_0_old)
                                        (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                        (reject$2_0 reject$2_0_old)
                                        (t.addr.i.0$2_0 t.addr.i.0$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (incdec.ptr.i$2_0 (+ t.addr.i.0$2_0 1)))
                                          (let
                                             ((t.addr.i.0$2_0 incdec.ptr.i$2_0))
                                             (let
                                                ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                (let
                                                   ((conv1.i$2_0 _$2_2)
                                                    (conv2.i$2_0 conv.i$2_0))
                                                   (let
                                                      ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                      (=>
                                                         (not cmp.i$2_0)
                                                         (let
                                                            ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                            (let
                                                               ((tobool.i$2_0 (distinct _$2_3 0)))
                                                               (=>
                                                                  (not tobool.i$2_0)
                                                                  (let
                                                                     ((retval.i.0$2_0 0))
                                                                     (let
                                                                        ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                        (=>
                                                                           cmp$2_0
                                                                           (let
                                                                              ((inc$2_0 (+ count.0$2_0 1)))
                                                                              (let
                                                                                 ((s.addr.0$2_0 incdec.ptr$2_0)
                                                                                  (count.0$2_0 inc$2_0))
                                                                                 (forall
                                                                                    ((i1 Int)
                                                                                     (i2 Int))
                                                                                    (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 i1 (select HEAP$1 i1) count.0$2_0 reject$2_0 s.addr.0$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                           ((i.0$1_0 0))
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                 (let
                                    ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((tobool2$1_0 (distinct _$1_1 0)))
                                       (=>
                                          tobool2$1_0
                                          (let
                                             ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                             (let
                                                ((conv4$1_0 _$1_2)
                                                 (idxprom5$1_0 i.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                                   (let
                                                      ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((conv7$1_0 _$1_3))
                                                         (let
                                                            ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                            (=>
                                                               cmp$1_0
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
                                                                                  (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                                                                 (let
                                                                                    ((conv1$2_0 _$2_1))
                                                                                    (let
                                                                                       ((conv.i$2_0 conv1$2_0)
                                                                                        (t.addr.i.0$2_0 reject$2_0))
                                                                                       (let
                                                                                          ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                          (let
                                                                                             ((conv1.i$2_0 _$2_2)
                                                                                              (conv2.i$2_0 conv.i$2_0))
                                                                                             (let
                                                                                                ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                                                (=>
                                                                                                   (not cmp.i$2_0)
                                                                                                   (let
                                                                                                      ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                                      (let
                                                                                                         ((tobool.i$2_0 (distinct _$2_3 0)))
                                                                                                         (not tobool.i$2_0))))))))))))))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                                           (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                          (let
                                             ((conv1$2_0 _$2_1))
                                             (let
                                                ((conv.i$2_0 conv1$2_0)
                                                 (t.addr.i.0$2_0 reject$2_0))
                                                (let
                                                   ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                   (let
                                                      ((conv1.i$2_0 _$2_2)
                                                       (conv2.i$2_0 conv.i$2_0))
                                                      (let
                                                         ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                         (=>
                                                            (not cmp.i$2_0)
                                                            (let
                                                               ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                               (let
                                                                  ((tobool.i$2_0 (distinct _$2_3 0)))
                                                                  (not tobool.i$2_0)))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                           ((i.0$1_0 0))
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                 (let
                                    ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((tobool2$1_0 (distinct _$1_1 0)))
                                       (=>
                                          tobool2$1_0
                                          (let
                                             ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                             (let
                                                ((conv4$1_0 _$1_2)
                                                 (idxprom5$1_0 i.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                                   (let
                                                      ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((conv7$1_0 _$1_3))
                                                         (let
                                                            ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                            (=>
                                                               (not cmp$1_0)
                                                               (let
                                                                  ((count.0$2_0 count.0$2_0_old)
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
                                                                                  (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                                                                 (let
                                                                                    ((conv1$2_0 _$2_1))
                                                                                    (let
                                                                                       ((conv.i$2_0 conv1$2_0)
                                                                                        (t.addr.i.0$2_0 reject$2_0))
                                                                                       (let
                                                                                          ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                          (let
                                                                                             ((conv1.i$2_0 _$2_2)
                                                                                              (conv2.i$2_0 conv.i$2_0))
                                                                                             (let
                                                                                                ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                                                (=>
                                                                                                   cmp.i$2_0
                                                                                                   (let
                                                                                                      ((retval.i.0$2_0 t.addr.i.0$2_0))
                                                                                                      (let
                                                                                                         ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                                                         (=>
                                                                                                            (not cmp$2_0)
                                                                                                            (let
                                                                                                               ((result$2 count.0$2_0)
                                                                                                                (HEAP$2_res HEAP$2))
                                                                                                               false)))))))))))))))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                           ((i.0$1_0 0))
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                 (let
                                    ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((tobool2$1_0 (distinct _$1_1 0)))
                                       (=>
                                          tobool2$1_0
                                          (let
                                             ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                             (let
                                                ((conv4$1_0 _$1_2)
                                                 (idxprom5$1_0 i.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                                   (let
                                                      ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((conv7$1_0 _$1_3))
                                                         (let
                                                            ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                            (=>
                                                               (not cmp$1_0)
                                                               (let
                                                                  ((count.0$2_0 count.0$2_0_old)
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
                                                                                  (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                                                                 (let
                                                                                    ((conv1$2_0 _$2_1))
                                                                                    (let
                                                                                       ((conv.i$2_0 conv1$2_0)
                                                                                        (t.addr.i.0$2_0 reject$2_0))
                                                                                       (let
                                                                                          ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                          (let
                                                                                             ((conv1.i$2_0 _$2_2)
                                                                                              (conv2.i$2_0 conv.i$2_0))
                                                                                             (let
                                                                                                ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                                                (=>
                                                                                                   (not cmp.i$2_0)
                                                                                                   (let
                                                                                                      ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                                      (let
                                                                                                         ((tobool.i$2_0 (distinct _$2_3 0)))
                                                                                                         (=>
                                                                                                            (not tobool.i$2_0)
                                                                                                            (let
                                                                                                               ((retval.i.0$2_0 0))
                                                                                                               (let
                                                                                                                  ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                                                                  (=>
                                                                                                                     (not cmp$2_0)
                                                                                                                     (let
                                                                                                                        ((result$2 count.0$2_0)
                                                                                                                         (HEAP$2_res HEAP$2))
                                                                                                                        false))))))))))))))))))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                           ((i.0$1_0 0))
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                 (let
                                    ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((tobool2$1_0 (distinct _$1_1 0)))
                                       (=>
                                          tobool2$1_0
                                          (let
                                             ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                             (let
                                                ((conv4$1_0 _$1_2)
                                                 (idxprom5$1_0 i.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                                   (let
                                                      ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((conv7$1_0 _$1_3))
                                                         (let
                                                            ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                            (=>
                                                               (not cmp$1_0)
                                                               (let
                                                                  ((count.0$2_0 count.0$2_0_old)
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
                                                                                 false)))))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                           ((i.0$1_0 0))
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                 (let
                                    ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((tobool2$1_0 (distinct _$1_1 0)))
                                       (=>
                                          tobool2$1_0
                                          (let
                                             ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                             (let
                                                ((conv4$1_0 _$1_2)
                                                 (idxprom5$1_0 i.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                                   (let
                                                      ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((conv7$1_0 _$1_3))
                                                         (let
                                                            ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                            (=>
                                                               cmp$1_0
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
                                                                                  (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                                                                 (let
                                                                                    ((conv1$2_0 _$2_1))
                                                                                    (let
                                                                                       ((conv.i$2_0 conv1$2_0)
                                                                                        (t.addr.i.0$2_0 reject$2_0))
                                                                                       (let
                                                                                          ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                          (let
                                                                                             ((conv1.i$2_0 _$2_2)
                                                                                              (conv2.i$2_0 conv.i$2_0))
                                                                                             (let
                                                                                                ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                                                (=>
                                                                                                   cmp.i$2_0
                                                                                                   (let
                                                                                                      ((retval.i.0$2_0 t.addr.i.0$2_0))
                                                                                                      (let
                                                                                                         ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                                                         (=>
                                                                                                            (not cmp$2_0)
                                                                                                            (let
                                                                                                               ((result$2 count.0$2_0)
                                                                                                                (HEAP$2_res HEAP$2))
                                                                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                           ((i.0$1_0 0))
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                 (let
                                    ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((tobool2$1_0 (distinct _$1_1 0)))
                                       (=>
                                          tobool2$1_0
                                          (let
                                             ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                             (let
                                                ((conv4$1_0 _$1_2)
                                                 (idxprom5$1_0 i.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                                   (let
                                                      ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((conv7$1_0 _$1_3))
                                                         (let
                                                            ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                            (=>
                                                               cmp$1_0
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
                                                                                  (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                                                                 (let
                                                                                    ((conv1$2_0 _$2_1))
                                                                                    (let
                                                                                       ((conv.i$2_0 conv1$2_0)
                                                                                        (t.addr.i.0$2_0 reject$2_0))
                                                                                       (let
                                                                                          ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                          (let
                                                                                             ((conv1.i$2_0 _$2_2)
                                                                                              (conv2.i$2_0 conv.i$2_0))
                                                                                             (let
                                                                                                ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                                                (=>
                                                                                                   (not cmp.i$2_0)
                                                                                                   (let
                                                                                                      ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                                      (let
                                                                                                         ((tobool.i$2_0 (distinct _$2_3 0)))
                                                                                                         (=>
                                                                                                            (not tobool.i$2_0)
                                                                                                            (let
                                                                                                               ((retval.i.0$2_0 0))
                                                                                                               (let
                                                                                                                  ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                                                                  (=>
                                                                                                                     (not cmp$2_0)
                                                                                                                     (let
                                                                                                                        ((result$2 count.0$2_0)
                                                                                                                         (HEAP$2_res HEAP$2))
                                                                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                           ((i.0$1_0 0))
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                 (let
                                    ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((tobool2$1_0 (distinct _$1_1 0)))
                                       (=>
                                          tobool2$1_0
                                          (let
                                             ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                             (let
                                                ((conv4$1_0 _$1_2)
                                                 (idxprom5$1_0 i.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                                   (let
                                                      ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((conv7$1_0 _$1_3))
                                                         (let
                                                            ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                            (=>
                                                               cmp$1_0
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
                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                                           (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                          (let
                                             ((conv1$2_0 _$2_1))
                                             (let
                                                ((conv.i$2_0 conv1$2_0)
                                                 (t.addr.i.0$2_0 reject$2_0))
                                                (let
                                                   ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                   (let
                                                      ((conv1.i$2_0 _$2_2)
                                                       (conv2.i$2_0 conv.i$2_0))
                                                      (let
                                                         ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                         (=>
                                                            cmp.i$2_0
                                                            (let
                                                               ((retval.i.0$2_0 t.addr.i.0$2_0))
                                                               (let
                                                                  ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                  (=>
                                                                     (not cmp$2_0)
                                                                     (let
                                                                        ((result$2 count.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                                           (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                          (let
                                             ((conv1$2_0 _$2_1))
                                             (let
                                                ((conv.i$2_0 conv1$2_0)
                                                 (t.addr.i.0$2_0 reject$2_0))
                                                (let
                                                   ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                   (let
                                                      ((conv1.i$2_0 _$2_2)
                                                       (conv2.i$2_0 conv.i$2_0))
                                                      (let
                                                         ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                         (=>
                                                            (not cmp.i$2_0)
                                                            (let
                                                               ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                               (let
                                                                  ((tobool.i$2_0 (distinct _$2_3 0)))
                                                                  (=>
                                                                     (not tobool.i$2_0)
                                                                     (let
                                                                        ((retval.i.0$2_0 0))
                                                                        (let
                                                                           ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                           (=>
                                                                              (not cmp$2_0)
                                                                              (let
                                                                                 ((result$2 count.0$2_0)
                                                                                  (HEAP$2_res HEAP$2))
                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                           ((i.0$1_0 0))
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                 (let
                                    ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((tobool2$1_0 (distinct _$1_1 0)))
                                       (=>
                                          tobool2$1_0
                                          (let
                                             ((_$1_2 (select HEAP$1 s.addr.0$1_0)))
                                             (let
                                                ((conv4$1_0 _$1_2)
                                                 (idxprom5$1_0 i.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ reject$1_0 idxprom5$1_0)))
                                                   (let
                                                      ((_$1_3 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((conv7$1_0 _$1_3))
                                                         (let
                                                            ((cmp$1_0 (= conv4$1_0 conv7$1_0)))
                                                            (=>
                                                               (not cmp$1_0)
                                                               (let
                                                                  ((count.0$2_0 count.0$2_0_old)
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
                                                                                  (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                                                                 (let
                                                                                    ((conv1$2_0 _$2_1))
                                                                                    (let
                                                                                       ((conv.i$2_0 conv1$2_0)
                                                                                        (t.addr.i.0$2_0 reject$2_0))
                                                                                       (let
                                                                                          ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                          (let
                                                                                             ((conv1.i$2_0 _$2_2)
                                                                                              (conv2.i$2_0 conv.i$2_0))
                                                                                             (let
                                                                                                ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                                                (=>
                                                                                                   (not cmp.i$2_0)
                                                                                                   (let
                                                                                                      ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                                      (let
                                                                                                         ((tobool.i$2_0 (distinct _$2_3 0)))
                                                                                                         (=>
                                                                                                            tobool.i$2_0
                                                                                                            (forall
                                                                                                               ((i1 Int)
                                                                                                                (i2 Int))
                                                                                                               (INV_MAIN_0 count.0$1_0 i.0$1_0 reject$1_0 s.addr.0$1_0 i1 (select HEAP$1 i1) conv.i$2_0 count.0$2_0 incdec.ptr$2_0 reject$2_0 t.addr.i.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                           ((i.0$1_0 0))
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                 (let
                                    ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((tobool2$1_0 (distinct _$1_1 0)))
                                       (=>
                                          (not tobool2$1_0)
                                          (let
                                             ((inc10$1_0 (+ count.0$1_0 1))
                                              (incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                             (let
                                                ((count.0$1_0 inc10$1_0)
                                                 (s.addr.0$1_0 incdec.ptr$1_0)
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
                                                                (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                                               (let
                                                                  ((conv1$2_0 _$2_1))
                                                                  (let
                                                                     ((conv.i$2_0 conv1$2_0)
                                                                      (t.addr.i.0$2_0 reject$2_0))
                                                                     (let
                                                                        ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                        (let
                                                                           ((conv1.i$2_0 _$2_2)
                                                                            (conv2.i$2_0 conv.i$2_0))
                                                                           (let
                                                                              ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                              (=>
                                                                                 cmp.i$2_0
                                                                                 (let
                                                                                    ((retval.i.0$2_0 t.addr.i.0$2_0))
                                                                                    (let
                                                                                       ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                                       (=>
                                                                                          cmp$2_0
                                                                                          (let
                                                                                             ((inc$2_0 (+ count.0$2_0 1)))
                                                                                             (let
                                                                                                ((s.addr.0$2_0 incdec.ptr$2_0)
                                                                                                 (count.0$2_0 inc$2_0))
                                                                                                (forall
                                                                                                   ((i1 Int)
                                                                                                    (i2 Int))
                                                                                                   (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 i1 (select HEAP$1 i1) count.0$2_0 reject$2_0 s.addr.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                           ((i.0$1_0 0))
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                 (let
                                    ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((tobool2$1_0 (distinct _$1_1 0)))
                                       (=>
                                          (not tobool2$1_0)
                                          (let
                                             ((inc10$1_0 (+ count.0$1_0 1))
                                              (incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                             (let
                                                ((count.0$1_0 inc10$1_0)
                                                 (s.addr.0$1_0 incdec.ptr$1_0)
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
                                                                (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                                               (let
                                                                  ((conv1$2_0 _$2_1))
                                                                  (let
                                                                     ((conv.i$2_0 conv1$2_0)
                                                                      (t.addr.i.0$2_0 reject$2_0))
                                                                     (let
                                                                        ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                        (let
                                                                           ((conv1.i$2_0 _$2_2)
                                                                            (conv2.i$2_0 conv.i$2_0))
                                                                           (let
                                                                              ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                              (=>
                                                                                 (not cmp.i$2_0)
                                                                                 (let
                                                                                    ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                    (let
                                                                                       ((tobool.i$2_0 (distinct _$2_3 0)))
                                                                                       (=>
                                                                                          (not tobool.i$2_0)
                                                                                          (let
                                                                                             ((retval.i.0$2_0 0))
                                                                                             (let
                                                                                                ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                                                (=>
                                                                                                   cmp$2_0
                                                                                                   (let
                                                                                                      ((inc$2_0 (+ count.0$2_0 1)))
                                                                                                      (let
                                                                                                         ((s.addr.0$2_0 incdec.ptr$2_0)
                                                                                                          (count.0$2_0 inc$2_0))
                                                                                                         (forall
                                                                                                            ((i1 Int)
                                                                                                             (i2 Int))
                                                                                                            (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 i1 (select HEAP$1 i1) count.0$2_0 reject$2_0 s.addr.0$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
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
                           ((i.0$1_0 0))
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                 (let
                                    ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((tobool2$1_0 (distinct _$1_1 0)))
                                       (=>
                                          (not tobool2$1_0)
                                          (let
                                             ((inc10$1_0 (+ count.0$1_0 1))
                                              (incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                             (let
                                                ((count.0$1_0 inc10$1_0)
                                                 (s.addr.0$1_0 incdec.ptr$1_0))
                                                (=>
                                                   (and
                                                      (let
                                                         ((count.0$2_0 count.0$2_0_old)
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
                                                                         (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                                                        (let
                                                                           ((conv1$2_0 _$2_1))
                                                                           (let
                                                                              ((conv.i$2_0 conv1$2_0)
                                                                               (t.addr.i.0$2_0 reject$2_0))
                                                                              (let
                                                                                 ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                 (let
                                                                                    ((conv1.i$2_0 _$2_2)
                                                                                     (conv2.i$2_0 conv.i$2_0))
                                                                                    (let
                                                                                       ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                                       (=>
                                                                                          cmp.i$2_0
                                                                                          (let
                                                                                             ((retval.i.0$2_0 t.addr.i.0$2_0))
                                                                                             (let
                                                                                                ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                                                (=>
                                                                                                   cmp$2_0
                                                                                                   (let
                                                                                                      ((inc$2_0 (+ count.0$2_0 1)))
                                                                                                      (let
                                                                                                         ((s.addr.0$2_0 incdec.ptr$2_0)
                                                                                                          (count.0$2_0 inc$2_0))
                                                                                                         false)))))))))))))))))
                                                      (let
                                                         ((count.0$2_0 count.0$2_0_old)
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
                                                                         (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                                                                        (let
                                                                           ((conv1$2_0 _$2_1))
                                                                           (let
                                                                              ((conv.i$2_0 conv1$2_0)
                                                                               (t.addr.i.0$2_0 reject$2_0))
                                                                              (let
                                                                                 ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                 (let
                                                                                    ((conv1.i$2_0 _$2_2)
                                                                                     (conv2.i$2_0 conv.i$2_0))
                                                                                    (let
                                                                                       ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                                                                       (=>
                                                                                          (not cmp.i$2_0)
                                                                                          (let
                                                                                             ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                                                             (let
                                                                                                ((tobool.i$2_0 (distinct _$2_3 0)))
                                                                                                (=>
                                                                                                   (not tobool.i$2_0)
                                                                                                   (let
                                                                                                      ((retval.i.0$2_0 0))
                                                                                                      (let
                                                                                                         ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                                                                         (=>
                                                                                                            cmp$2_0
                                                                                                            (let
                                                                                                               ((inc$2_0 (+ count.0$2_0 1)))
                                                                                                               (let
                                                                                                                  ((s.addr.0$2_0 incdec.ptr$2_0)
                                                                                                                   (count.0$2_0 inc$2_0))
                                                                                                                  false)))))))))))))))))))))
                                                   (forall
                                                      ((i1 Int)
                                                       (i2_old Int))
                                                      (INV_MAIN_1 count.0$1_0 reject$1_0 s.addr.0$1_0 i1 (select HEAP$1 i1) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((count.0$2_0 count.0$2_0_old)
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
                            (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                           (let
                              ((conv1$2_0 _$2_1))
                              (let
                                 ((conv.i$2_0 conv1$2_0)
                                  (t.addr.i.0$2_0 reject$2_0))
                                 (let
                                    ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                    (let
                                       ((conv1.i$2_0 _$2_2)
                                        (conv2.i$2_0 conv.i$2_0))
                                       (let
                                          ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                          (=>
                                             cmp.i$2_0
                                             (let
                                                ((retval.i.0$2_0 t.addr.i.0$2_0))
                                                (let
                                                   ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                   (=>
                                                      cmp$2_0
                                                      (let
                                                         ((inc$2_0 (+ count.0$2_0 1)))
                                                         (let
                                                            ((s.addr.0$2_0 incdec.ptr$2_0)
                                                             (count.0$2_0 inc$2_0))
                                                            (=>
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
                                                                                 ((i.0$1_0 0))
                                                                                 (let
                                                                                    ((idxprom$1_0 i.0$1_0))
                                                                                    (let
                                                                                       ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                                                                       (let
                                                                                          ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                                                                          (let
                                                                                             ((tobool2$1_0 (distinct _$1_1 0)))
                                                                                             (=>
                                                                                                (not tobool2$1_0)
                                                                                                (let
                                                                                                   ((inc10$1_0 (+ count.0$1_0 1))
                                                                                                    (incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                                                                                   (let
                                                                                                      ((count.0$1_0 inc10$1_0)
                                                                                                       (s.addr.0$1_0 incdec.ptr$1_0))
                                                                                                      false)))))))))))))
                                                               (forall
                                                                  ((i1_old Int)
                                                                   (i2 Int))
                                                                  (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0 reject$2_0 s.addr.0$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))
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
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0_old reject$2_0_old s.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((count.0$2_0 count.0$2_0_old)
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
                            (_$2_1 (select HEAP$2 s.addr.0$2_0)))
                           (let
                              ((conv1$2_0 _$2_1))
                              (let
                                 ((conv.i$2_0 conv1$2_0)
                                  (t.addr.i.0$2_0 reject$2_0))
                                 (let
                                    ((_$2_2 (select HEAP$2 t.addr.i.0$2_0)))
                                    (let
                                       ((conv1.i$2_0 _$2_2)
                                        (conv2.i$2_0 conv.i$2_0))
                                       (let
                                          ((cmp.i$2_0 (= conv1.i$2_0 conv2.i$2_0)))
                                          (=>
                                             (not cmp.i$2_0)
                                             (let
                                                ((_$2_3 (select HEAP$2 t.addr.i.0$2_0)))
                                                (let
                                                   ((tobool.i$2_0 (distinct _$2_3 0)))
                                                   (=>
                                                      (not tobool.i$2_0)
                                                      (let
                                                         ((retval.i.0$2_0 0))
                                                         (let
                                                            ((cmp$2_0 (= retval.i.0$2_0 0)))
                                                            (=>
                                                               cmp$2_0
                                                               (let
                                                                  ((inc$2_0 (+ count.0$2_0 1)))
                                                                  (let
                                                                     ((s.addr.0$2_0 incdec.ptr$2_0)
                                                                      (count.0$2_0 inc$2_0))
                                                                     (=>
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
                                                                                          ((i.0$1_0 0))
                                                                                          (let
                                                                                             ((idxprom$1_0 i.0$1_0))
                                                                                             (let
                                                                                                ((arrayidx$1_0 (+ reject$1_0 idxprom$1_0)))
                                                                                                (let
                                                                                                   ((_$1_1 (select HEAP$1 arrayidx$1_0)))
                                                                                                   (let
                                                                                                      ((tobool2$1_0 (distinct _$1_1 0)))
                                                                                                      (=>
                                                                                                         (not tobool2$1_0)
                                                                                                         (let
                                                                                                            ((inc10$1_0 (+ count.0$1_0 1))
                                                                                                             (incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                                                                                            (let
                                                                                                               ((count.0$1_0 inc10$1_0)
                                                                                                                (s.addr.0$1_0 incdec.ptr$1_0))
                                                                                                               false)))))))))))))
                                                                        (forall
                                                                           ((i1_old Int)
                                                                            (i2 Int))
                                                                           (INV_MAIN_1 count.0$1_0_old reject$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) count.0$2_0 reject$2_0 s.addr.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))
(check-sat)
(get-model)
