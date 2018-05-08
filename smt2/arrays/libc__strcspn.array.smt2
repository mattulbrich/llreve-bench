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
; :annot (INV_MAIN_0 p.0$1_0 reject$1_0 s$1_0 HEAP$1 l.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_0
   (Int
    Int
    Int
    (Array Int Int)
    Int
    Int
    Int
    (Array Int Int))
   Bool)
; :annot (INV_MAIN_1 _$1_1 incdec.ptr$1_0 incdec.ptr1$1_0 reject$1_0 s$1_0 HEAP$1 i.0$2_0 l.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_1
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
                (p.0$1_0 s$1_0)
                (s$2_0 s$2_0_old))
               (let
                  ((reject$2_0 reject$2_0_old)
                   (HEAP$2 HEAP$2_old)
                   (l.0$2_0 0)
                   (s.addr.0$2_0 s$2_0))
                  (INV_MAIN_0 p.0$1_0 reject$1_0 s$1_0 HEAP$1 l.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2)))))))
(assert
   (forall
      ((p.0$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((p.0$1_0 p.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 p.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        tobool$1_0
                        (let
                           ((incdec.ptr$1_0 (+ p.0$1_0 1))
                            (_$1_1 (select HEAP$1 p.0$1_0))
                            (spanp.0$1_0 reject$1_0))
                           (let
                              ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                               (_$1_2 (select HEAP$1 spanp.0$1_0)))
                              (let
                                 ((conv2$1_0 _$1_2)
                                  (conv3$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                                    (=>
                                       cmp$1_0
                                       (let
                                          ((add.ptr$1_0 (+ incdec.ptr$1_0 (- 1))))
                                          (let
                                             ((sub.ptr.lhs.cast$1_0 add.ptr$1_0)
                                              (sub.ptr.rhs.cast$1_0 s$1_0))
                                             (let
                                                ((sub.ptr.sub$1_0 (- sub.ptr.lhs.cast$1_0 sub.ptr.rhs.cast$1_0)))
                                                (let
                                                   ((retval.0$1_0 sub.ptr.sub$1_0))
                                                   (let
                                                      ((result$1 retval.0$1_0)
                                                       (HEAP$1_res HEAP$1)
                                                       (l.0$2_0 l.0$2_0_old)
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
                                                                     ((i.0$2_0 0))
                                                                     (let
                                                                        ((idxprom$2_0 i.0$2_0))
                                                                        (let
                                                                           ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                                           (let
                                                                              ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                                              (let
                                                                                 ((tobool2$2_0 (distinct _$2_1 0)))
                                                                                 (=>
                                                                                    tobool2$2_0
                                                                                    (let
                                                                                       ((_$2_2 (select HEAP$2 s.addr.0$2_0)))
                                                                                       (let
                                                                                          ((conv4$2_0 _$2_2)
                                                                                           (idxprom5$2_0 i.0$2_0))
                                                                                          (let
                                                                                             ((arrayidx6$2_0 (+ reject$2_0 idxprom5$2_0)))
                                                                                             (let
                                                                                                ((_$2_3 (select HEAP$2 arrayidx6$2_0)))
                                                                                                (let
                                                                                                   ((conv7$2_0 _$2_3))
                                                                                                   (let
                                                                                                      ((cmp$2_0 (= conv4$2_0 conv7$2_0)))
                                                                                                      (not (not cmp$2_0))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((p.0$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((p.0$1_0 p.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 p.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        (not tobool$1_0)
                        (let
                           ((retval.0$1_0 0))
                           (let
                              ((result$1 retval.0$1_0)
                               (HEAP$1_res HEAP$1)
                               (l.0$2_0 l.0$2_0_old)
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
                                             ((i.0$2_0 0))
                                             (let
                                                ((idxprom$2_0 i.0$2_0))
                                                (let
                                                   ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                   (let
                                                      ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                      (let
                                                         ((tobool2$2_0 (distinct _$2_1 0)))
                                                         (=>
                                                            tobool2$2_0
                                                            (let
                                                               ((_$2_2 (select HEAP$2 s.addr.0$2_0)))
                                                               (let
                                                                  ((conv4$2_0 _$2_2)
                                                                   (idxprom5$2_0 i.0$2_0))
                                                                  (let
                                                                     ((arrayidx6$2_0 (+ reject$2_0 idxprom5$2_0)))
                                                                     (let
                                                                        ((_$2_3 (select HEAP$2 arrayidx6$2_0)))
                                                                        (let
                                                                           ((conv7$2_0 _$2_3))
                                                                           (let
                                                                              ((cmp$2_0 (= conv4$2_0 conv7$2_0)))
                                                                              (not (not cmp$2_0))))))))))))))))))))))))))))
(assert
   (forall
      ((p.0$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((p.0$1_0 p.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 p.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        tobool$1_0
                        (let
                           ((incdec.ptr$1_0 (+ p.0$1_0 1))
                            (_$1_1 (select HEAP$1 p.0$1_0))
                            (spanp.0$1_0 reject$1_0))
                           (let
                              ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                               (_$1_2 (select HEAP$1 spanp.0$1_0)))
                              (let
                                 ((conv2$1_0 _$1_2)
                                  (conv3$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                                    (=>
                                       (not cmp$1_0)
                                       (let
                                          ((conv5$1_0 _$1_2))
                                          (let
                                             ((cmp6$1_0 (distinct conv5$1_0 0)))
                                             (=>
                                                cmp6$1_0
                                                (let
                                                   ((l.0$2_0 l.0$2_0_old)
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
                                                                  ((i.0$2_0 0))
                                                                  (let
                                                                     ((idxprom$2_0 i.0$2_0))
                                                                     (let
                                                                        ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                                        (let
                                                                           ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                                           (let
                                                                              ((tobool2$2_0 (distinct _$2_1 0)))
                                                                              (=>
                                                                                 tobool2$2_0
                                                                                 (let
                                                                                    ((_$2_2 (select HEAP$2 s.addr.0$2_0)))
                                                                                    (let
                                                                                       ((conv4$2_0 _$2_2)
                                                                                        (idxprom5$2_0 i.0$2_0))
                                                                                       (let
                                                                                          ((arrayidx6$2_0 (+ reject$2_0 idxprom5$2_0)))
                                                                                          (let
                                                                                             ((_$2_3 (select HEAP$2 arrayidx6$2_0)))
                                                                                             (let
                                                                                                ((conv7$2_0 _$2_3))
                                                                                                (let
                                                                                                   ((cmp$2_0 (= conv4$2_0 conv7$2_0)))
                                                                                                   (=>
                                                                                                      cmp$2_0
                                                                                                      (let
                                                                                                         ((retval.0$2_0 l.0$2_0))
                                                                                                         (let
                                                                                                            ((result$2 retval.0$2_0)
                                                                                                             (HEAP$2_res HEAP$2))
                                                                                                            false))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((p.0$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((p.0$1_0 p.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 p.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        tobool$1_0
                        (let
                           ((incdec.ptr$1_0 (+ p.0$1_0 1))
                            (_$1_1 (select HEAP$1 p.0$1_0))
                            (spanp.0$1_0 reject$1_0))
                           (let
                              ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                               (_$1_2 (select HEAP$1 spanp.0$1_0)))
                              (let
                                 ((conv2$1_0 _$1_2)
                                  (conv3$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                                    (=>
                                       (not cmp$1_0)
                                       (let
                                          ((conv5$1_0 _$1_2))
                                          (let
                                             ((cmp6$1_0 (distinct conv5$1_0 0)))
                                             (=>
                                                cmp6$1_0
                                                (let
                                                   ((l.0$2_0 l.0$2_0_old)
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
                                                                  ((retval.0$2_0 0))
                                                                  (let
                                                                     ((result$2 retval.0$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     false)))))))))))))))))))))))
(assert
   (forall
      ((p.0$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((p.0$1_0 p.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 p.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        tobool$1_0
                        (let
                           ((incdec.ptr$1_0 (+ p.0$1_0 1))
                            (_$1_1 (select HEAP$1 p.0$1_0))
                            (spanp.0$1_0 reject$1_0))
                           (let
                              ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                               (_$1_2 (select HEAP$1 spanp.0$1_0)))
                              (let
                                 ((conv2$1_0 _$1_2)
                                  (conv3$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                                    (=>
                                       cmp$1_0
                                       (let
                                          ((add.ptr$1_0 (+ incdec.ptr$1_0 (- 1))))
                                          (let
                                             ((sub.ptr.lhs.cast$1_0 add.ptr$1_0)
                                              (sub.ptr.rhs.cast$1_0 s$1_0))
                                             (let
                                                ((sub.ptr.sub$1_0 (- sub.ptr.lhs.cast$1_0 sub.ptr.rhs.cast$1_0)))
                                                (let
                                                   ((retval.0$1_0 sub.ptr.sub$1_0))
                                                   (let
                                                      ((result$1 retval.0$1_0)
                                                       (HEAP$1_res HEAP$1)
                                                       (l.0$2_0 l.0$2_0_old)
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
                                                                     ((i.0$2_0 0))
                                                                     (let
                                                                        ((idxprom$2_0 i.0$2_0))
                                                                        (let
                                                                           ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                                           (let
                                                                              ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                                              (let
                                                                                 ((tobool2$2_0 (distinct _$2_1 0)))
                                                                                 (=>
                                                                                    tobool2$2_0
                                                                                    (let
                                                                                       ((_$2_2 (select HEAP$2 s.addr.0$2_0)))
                                                                                       (let
                                                                                          ((conv4$2_0 _$2_2)
                                                                                           (idxprom5$2_0 i.0$2_0))
                                                                                          (let
                                                                                             ((arrayidx6$2_0 (+ reject$2_0 idxprom5$2_0)))
                                                                                             (let
                                                                                                ((_$2_3 (select HEAP$2 arrayidx6$2_0)))
                                                                                                (let
                                                                                                   ((conv7$2_0 _$2_3))
                                                                                                   (let
                                                                                                      ((cmp$2_0 (= conv4$2_0 conv7$2_0)))
                                                                                                      (=>
                                                                                                         cmp$2_0
                                                                                                         (let
                                                                                                            ((retval.0$2_0 l.0$2_0))
                                                                                                            (let
                                                                                                               ((result$2 retval.0$2_0)
                                                                                                                (HEAP$2_res HEAP$2))
                                                                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((p.0$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((p.0$1_0 p.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 p.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        tobool$1_0
                        (let
                           ((incdec.ptr$1_0 (+ p.0$1_0 1))
                            (_$1_1 (select HEAP$1 p.0$1_0))
                            (spanp.0$1_0 reject$1_0))
                           (let
                              ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                               (_$1_2 (select HEAP$1 spanp.0$1_0)))
                              (let
                                 ((conv2$1_0 _$1_2)
                                  (conv3$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                                    (=>
                                       cmp$1_0
                                       (let
                                          ((add.ptr$1_0 (+ incdec.ptr$1_0 (- 1))))
                                          (let
                                             ((sub.ptr.lhs.cast$1_0 add.ptr$1_0)
                                              (sub.ptr.rhs.cast$1_0 s$1_0))
                                             (let
                                                ((sub.ptr.sub$1_0 (- sub.ptr.lhs.cast$1_0 sub.ptr.rhs.cast$1_0)))
                                                (let
                                                   ((retval.0$1_0 sub.ptr.sub$1_0))
                                                   (let
                                                      ((result$1 retval.0$1_0)
                                                       (HEAP$1_res HEAP$1)
                                                       (l.0$2_0 l.0$2_0_old)
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
                                                                     ((retval.0$2_0 0))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((p.0$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((p.0$1_0 p.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 p.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        (not tobool$1_0)
                        (let
                           ((retval.0$1_0 0))
                           (let
                              ((result$1 retval.0$1_0)
                               (HEAP$1_res HEAP$1)
                               (l.0$2_0 l.0$2_0_old)
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
                                             ((i.0$2_0 0))
                                             (let
                                                ((idxprom$2_0 i.0$2_0))
                                                (let
                                                   ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                   (let
                                                      ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                      (let
                                                         ((tobool2$2_0 (distinct _$2_1 0)))
                                                         (=>
                                                            tobool2$2_0
                                                            (let
                                                               ((_$2_2 (select HEAP$2 s.addr.0$2_0)))
                                                               (let
                                                                  ((conv4$2_0 _$2_2)
                                                                   (idxprom5$2_0 i.0$2_0))
                                                                  (let
                                                                     ((arrayidx6$2_0 (+ reject$2_0 idxprom5$2_0)))
                                                                     (let
                                                                        ((_$2_3 (select HEAP$2 arrayidx6$2_0)))
                                                                        (let
                                                                           ((conv7$2_0 _$2_3))
                                                                           (let
                                                                              ((cmp$2_0 (= conv4$2_0 conv7$2_0)))
                                                                              (=>
                                                                                 cmp$2_0
                                                                                 (let
                                                                                    ((retval.0$2_0 l.0$2_0))
                                                                                    (let
                                                                                       ((result$2 retval.0$2_0)
                                                                                        (HEAP$2_res HEAP$2))
                                                                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))
(assert
   (forall
      ((p.0$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((p.0$1_0 p.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 p.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        (not tobool$1_0)
                        (let
                           ((retval.0$1_0 0))
                           (let
                              ((result$1 retval.0$1_0)
                               (HEAP$1_res HEAP$1)
                               (l.0$2_0 l.0$2_0_old)
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
                                             ((retval.0$2_0 0))
                                             (let
                                                ((result$2 retval.0$2_0)
                                                 (HEAP$2_res HEAP$2))
                                                (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))
(assert
   (forall
      ((p.0$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((p.0$1_0 p.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 p.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        tobool$1_0
                        (let
                           ((incdec.ptr$1_0 (+ p.0$1_0 1))
                            (_$1_1 (select HEAP$1 p.0$1_0))
                            (spanp.0$1_0 reject$1_0))
                           (let
                              ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                               (_$1_2 (select HEAP$1 spanp.0$1_0)))
                              (let
                                 ((conv2$1_0 _$1_2)
                                  (conv3$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                                    (=>
                                       (not cmp$1_0)
                                       (let
                                          ((conv5$1_0 _$1_2))
                                          (let
                                             ((cmp6$1_0 (distinct conv5$1_0 0)))
                                             (=>
                                                (not cmp6$1_0)
                                                (let
                                                   ((p.0$1_0 incdec.ptr$1_0)
                                                    (l.0$2_0 l.0$2_0_old)
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
                                                                  ((i.0$2_0 0))
                                                                  (let
                                                                     ((idxprom$2_0 i.0$2_0))
                                                                     (let
                                                                        ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                                        (let
                                                                           ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                                           (let
                                                                              ((tobool2$2_0 (distinct _$2_1 0)))
                                                                              (=>
                                                                                 (not tobool2$2_0)
                                                                                 (let
                                                                                    ((inc10$2_0 (+ l.0$2_0 1))
                                                                                     (incdec.ptr$2_0 (+ s.addr.0$2_0 1)))
                                                                                    (let
                                                                                       ((l.0$2_0 inc10$2_0)
                                                                                        (s.addr.0$2_0 incdec.ptr$2_0))
                                                                                       (INV_MAIN_0 p.0$1_0 reject$1_0 s$1_0 HEAP$1 l.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2))))))))))))))))))))))))))))))
(assert
   (forall
      ((p.0$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((p.0$1_0 p.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 p.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        tobool$1_0
                        (let
                           ((incdec.ptr$1_0 (+ p.0$1_0 1))
                            (_$1_1 (select HEAP$1 p.0$1_0))
                            (spanp.0$1_0 reject$1_0))
                           (let
                              ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                               (_$1_2 (select HEAP$1 spanp.0$1_0)))
                              (let
                                 ((conv2$1_0 _$1_2)
                                  (conv3$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                                    (=>
                                       (not cmp$1_0)
                                       (let
                                          ((conv5$1_0 _$1_2))
                                          (let
                                             ((cmp6$1_0 (distinct conv5$1_0 0)))
                                             (=>
                                                (not cmp6$1_0)
                                                (let
                                                   ((p.0$1_0 incdec.ptr$1_0))
                                                   (=>
                                                      (let
                                                         ((l.0$2_0 l.0$2_0_old)
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
                                                                        ((i.0$2_0 0))
                                                                        (let
                                                                           ((idxprom$2_0 i.0$2_0))
                                                                           (let
                                                                              ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                                              (let
                                                                                 ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                                                 (let
                                                                                    ((tobool2$2_0 (distinct _$2_1 0)))
                                                                                    (=>
                                                                                       (not tobool2$2_0)
                                                                                       (let
                                                                                          ((inc10$2_0 (+ l.0$2_0 1))
                                                                                           (incdec.ptr$2_0 (+ s.addr.0$2_0 1)))
                                                                                          (let
                                                                                             ((l.0$2_0 inc10$2_0)
                                                                                              (s.addr.0$2_0 incdec.ptr$2_0))
                                                                                             false)))))))))))))
                                                      (INV_MAIN_0 p.0$1_0 reject$1_0 s$1_0 HEAP$1 l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)))))))))))))))))))
(assert
   (forall
      ((p.0$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((l.0$2_0 l.0$2_0_old)
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
                           ((i.0$2_0 0))
                           (let
                              ((idxprom$2_0 i.0$2_0))
                              (let
                                 ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                 (let
                                    ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                    (let
                                       ((tobool2$2_0 (distinct _$2_1 0)))
                                       (=>
                                          (not tobool2$2_0)
                                          (let
                                             ((inc10$2_0 (+ l.0$2_0 1))
                                              (incdec.ptr$2_0 (+ s.addr.0$2_0 1)))
                                             (let
                                                ((l.0$2_0 inc10$2_0)
                                                 (s.addr.0$2_0 incdec.ptr$2_0))
                                                (=>
                                                   (let
                                                      ((p.0$1_0 p.0$1_0_old)
                                                       (reject$1_0 reject$1_0_old)
                                                       (s$1_0 s$1_0_old)
                                                       (HEAP$1 HEAP$1_old))
                                                      (let
                                                         ((_$1_0 (select HEAP$1 p.0$1_0)))
                                                         (let
                                                            ((conv$1_0 _$1_0))
                                                            (let
                                                               ((tobool$1_0 (distinct conv$1_0 0)))
                                                               (=>
                                                                  tobool$1_0
                                                                  (let
                                                                     ((incdec.ptr$1_0 (+ p.0$1_0 1))
                                                                      (_$1_1 (select HEAP$1 p.0$1_0))
                                                                      (spanp.0$1_0 reject$1_0))
                                                                     (let
                                                                        ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                                                                         (_$1_2 (select HEAP$1 spanp.0$1_0)))
                                                                        (let
                                                                           ((conv2$1_0 _$1_2)
                                                                            (conv3$1_0 _$1_1))
                                                                           (let
                                                                              ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                                                                              (=>
                                                                                 (not cmp$1_0)
                                                                                 (let
                                                                                    ((conv5$1_0 _$1_2))
                                                                                    (let
                                                                                       ((cmp6$1_0 (distinct conv5$1_0 0)))
                                                                                       (=>
                                                                                          (not cmp6$1_0)
                                                                                          (let
                                                                                             ((p.0$1_0 incdec.ptr$1_0))
                                                                                             false))))))))))))))
                                                   (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2))))))))))))))))))
(assert
   (forall
      ((p.0$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 p.0$1_0_old reject$1_0_old s$1_0_old HEAP$1_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((p.0$1_0 p.0$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 p.0$1_0)))
               (let
                  ((conv$1_0 _$1_0))
                  (let
                     ((tobool$1_0 (distinct conv$1_0 0)))
                     (=>
                        tobool$1_0
                        (let
                           ((incdec.ptr$1_0 (+ p.0$1_0 1))
                            (_$1_1 (select HEAP$1 p.0$1_0))
                            (spanp.0$1_0 reject$1_0))
                           (let
                              ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                               (_$1_2 (select HEAP$1 spanp.0$1_0)))
                              (let
                                 ((conv2$1_0 _$1_2)
                                  (conv3$1_0 _$1_1))
                                 (let
                                    ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                                    (=>
                                       (not cmp$1_0)
                                       (let
                                          ((conv5$1_0 _$1_2))
                                          (let
                                             ((cmp6$1_0 (distinct conv5$1_0 0)))
                                             (=>
                                                cmp6$1_0
                                                (let
                                                   ((l.0$2_0 l.0$2_0_old)
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
                                                                  ((i.0$2_0 0))
                                                                  (let
                                                                     ((idxprom$2_0 i.0$2_0))
                                                                     (let
                                                                        ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                                        (let
                                                                           ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                                           (let
                                                                              ((tobool2$2_0 (distinct _$2_1 0)))
                                                                              (=>
                                                                                 tobool2$2_0
                                                                                 (let
                                                                                    ((_$2_2 (select HEAP$2 s.addr.0$2_0)))
                                                                                    (let
                                                                                       ((conv4$2_0 _$2_2)
                                                                                        (idxprom5$2_0 i.0$2_0))
                                                                                       (let
                                                                                          ((arrayidx6$2_0 (+ reject$2_0 idxprom5$2_0)))
                                                                                          (let
                                                                                             ((_$2_3 (select HEAP$2 arrayidx6$2_0)))
                                                                                             (let
                                                                                                ((conv7$2_0 _$2_3))
                                                                                                (let
                                                                                                   ((cmp$2_0 (= conv4$2_0 conv7$2_0)))
                                                                                                   (=>
                                                                                                      (not cmp$2_0)
                                                                                                      (INV_MAIN_1 _$1_1 incdec.ptr$1_0 incdec.ptr1$1_0 reject$1_0 s$1_0 HEAP$1 i.0$2_0 l.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2)))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old reject$1_0_old s$1_0_old HEAP$1_old i.0$2_0_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool9$1_0 (distinct 1 0)))
            (=>
               tobool9$1_0
               (let
                  ((spanp.0$1_0 incdec.ptr1$1_0))
                  (let
                     ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                      (_$1_2 (select HEAP$1 spanp.0$1_0)))
                     (let
                        ((conv2$1_0 _$1_2)
                         (conv3$1_0 _$1_1))
                        (let
                           ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                           (=>
                              cmp$1_0
                              (let
                                 ((add.ptr$1_0 (+ incdec.ptr$1_0 (- 1))))
                                 (let
                                    ((sub.ptr.lhs.cast$1_0 add.ptr$1_0)
                                     (sub.ptr.rhs.cast$1_0 s$1_0))
                                    (let
                                       ((sub.ptr.sub$1_0 (- sub.ptr.lhs.cast$1_0 sub.ptr.rhs.cast$1_0)))
                                       (let
                                          ((retval.0$1_0 sub.ptr.sub$1_0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (i.0$2_0 i.0$2_0_old))
                                             (let
                                                ((l.0$2_0 l.0$2_0_old)
                                                 (reject$2_0 reject$2_0_old)
                                                 (s.addr.0$2_0 s.addr.0$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (inc$2_0 (+ i.0$2_0 1)))
                                                (let
                                                   ((i.0$2_0 inc$2_0))
                                                   (let
                                                      ((idxprom$2_0 i.0$2_0))
                                                      (let
                                                         ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                         (let
                                                            ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                            (let
                                                               ((tobool2$2_0 (distinct _$2_1 0)))
                                                               (=>
                                                                  (not tobool2$2_0)
                                                                  (let
                                                                     ((inc10$2_0 (+ l.0$2_0 1))
                                                                      (incdec.ptr$2_0 (+ s.addr.0$2_0 1)))
                                                                     (let
                                                                        ((l.0$2_0 inc10$2_0)
                                                                         (s.addr.0$2_0 incdec.ptr$2_0))
                                                                        false))))))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old reject$1_0_old s$1_0_old HEAP$1_old i.0$2_0_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool9$1_0 (distinct 1 0)))
            (=>
               tobool9$1_0
               (let
                  ((spanp.0$1_0 incdec.ptr1$1_0))
                  (let
                     ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                      (_$1_2 (select HEAP$1 spanp.0$1_0)))
                     (let
                        ((conv2$1_0 _$1_2)
                         (conv3$1_0 _$1_1))
                        (let
                           ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                           (=>
                              (not cmp$1_0)
                              (let
                                 ((conv5$1_0 _$1_2))
                                 (let
                                    ((cmp6$1_0 (distinct conv5$1_0 0)))
                                    (=>
                                       (not cmp6$1_0)
                                       (let
                                          ((p.0$1_0 incdec.ptr$1_0)
                                           (i.0$2_0 i.0$2_0_old))
                                          (let
                                             ((l.0$2_0 l.0$2_0_old)
                                              (reject$2_0 reject$2_0_old)
                                              (s.addr.0$2_0 s.addr.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (inc$2_0 (+ i.0$2_0 1)))
                                             (let
                                                ((i.0$2_0 inc$2_0))
                                                (let
                                                   ((idxprom$2_0 i.0$2_0))
                                                   (let
                                                      ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                      (let
                                                         ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                         (let
                                                            ((tobool2$2_0 (distinct _$2_1 0)))
                                                            (=>
                                                               tobool2$2_0
                                                               (let
                                                                  ((_$2_2 (select HEAP$2 s.addr.0$2_0)))
                                                                  (let
                                                                     ((conv4$2_0 _$2_2)
                                                                      (idxprom5$2_0 i.0$2_0))
                                                                     (let
                                                                        ((arrayidx6$2_0 (+ reject$2_0 idxprom5$2_0)))
                                                                        (let
                                                                           ((_$2_3 (select HEAP$2 arrayidx6$2_0)))
                                                                           (let
                                                                              ((conv7$2_0 _$2_3))
                                                                              (let
                                                                                 ((cmp$2_0 (= conv4$2_0 conv7$2_0)))
                                                                                 (=>
                                                                                    cmp$2_0
                                                                                    (let
                                                                                       ((retval.0$2_0 l.0$2_0))
                                                                                       (let
                                                                                          ((result$2 retval.0$2_0)
                                                                                           (HEAP$2_res HEAP$2))
                                                                                          false))))))))))))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old reject$1_0_old s$1_0_old HEAP$1_old i.0$2_0_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool9$1_0 (distinct 1 0)))
            (=>
               (not tobool9$1_0)
               (let
                  ((p.0$1_0 incdec.ptr$1_0)
                   (i.0$2_0 i.0$2_0_old))
                  (let
                     ((l.0$2_0 l.0$2_0_old)
                      (reject$2_0 reject$2_0_old)
                      (s.addr.0$2_0 s.addr.0$2_0_old)
                      (HEAP$2 HEAP$2_old)
                      (inc$2_0 (+ i.0$2_0 1)))
                     (let
                        ((i.0$2_0 inc$2_0))
                        (let
                           ((idxprom$2_0 i.0$2_0))
                           (let
                              ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                              (let
                                 ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                 (let
                                    ((tobool2$2_0 (distinct _$2_1 0)))
                                    (=>
                                       tobool2$2_0
                                       (let
                                          ((_$2_2 (select HEAP$2 s.addr.0$2_0)))
                                          (let
                                             ((conv4$2_0 _$2_2)
                                              (idxprom5$2_0 i.0$2_0))
                                             (let
                                                ((arrayidx6$2_0 (+ reject$2_0 idxprom5$2_0)))
                                                (let
                                                   ((_$2_3 (select HEAP$2 arrayidx6$2_0)))
                                                   (let
                                                      ((conv7$2_0 _$2_3))
                                                      (let
                                                         ((cmp$2_0 (= conv4$2_0 conv7$2_0)))
                                                         (=>
                                                            cmp$2_0
                                                            (let
                                                               ((retval.0$2_0 l.0$2_0))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  false))))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old reject$1_0_old s$1_0_old HEAP$1_old i.0$2_0_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool9$1_0 (distinct 1 0)))
            (=>
               tobool9$1_0
               (let
                  ((spanp.0$1_0 incdec.ptr1$1_0))
                  (let
                     ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                      (_$1_2 (select HEAP$1 spanp.0$1_0)))
                     (let
                        ((conv2$1_0 _$1_2)
                         (conv3$1_0 _$1_1))
                        (let
                           ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                           (=>
                              cmp$1_0
                              (let
                                 ((add.ptr$1_0 (+ incdec.ptr$1_0 (- 1))))
                                 (let
                                    ((sub.ptr.lhs.cast$1_0 add.ptr$1_0)
                                     (sub.ptr.rhs.cast$1_0 s$1_0))
                                    (let
                                       ((sub.ptr.sub$1_0 (- sub.ptr.lhs.cast$1_0 sub.ptr.rhs.cast$1_0)))
                                       (let
                                          ((retval.0$1_0 sub.ptr.sub$1_0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (i.0$2_0 i.0$2_0_old))
                                             (let
                                                ((l.0$2_0 l.0$2_0_old)
                                                 (reject$2_0 reject$2_0_old)
                                                 (s.addr.0$2_0 s.addr.0$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (inc$2_0 (+ i.0$2_0 1)))
                                                (let
                                                   ((i.0$2_0 inc$2_0))
                                                   (let
                                                      ((idxprom$2_0 i.0$2_0))
                                                      (let
                                                         ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                         (let
                                                            ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                            (let
                                                               ((tobool2$2_0 (distinct _$2_1 0)))
                                                               (=>
                                                                  tobool2$2_0
                                                                  (let
                                                                     ((_$2_2 (select HEAP$2 s.addr.0$2_0)))
                                                                     (let
                                                                        ((conv4$2_0 _$2_2)
                                                                         (idxprom5$2_0 i.0$2_0))
                                                                        (let
                                                                           ((arrayidx6$2_0 (+ reject$2_0 idxprom5$2_0)))
                                                                           (let
                                                                              ((_$2_3 (select HEAP$2 arrayidx6$2_0)))
                                                                              (let
                                                                                 ((conv7$2_0 _$2_3))
                                                                                 (let
                                                                                    ((cmp$2_0 (= conv4$2_0 conv7$2_0)))
                                                                                    (=>
                                                                                       cmp$2_0
                                                                                       (let
                                                                                          ((retval.0$2_0 l.0$2_0))
                                                                                          (let
                                                                                             ((result$2 retval.0$2_0)
                                                                                              (HEAP$2_res HEAP$2))
                                                                                             (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old reject$1_0_old s$1_0_old HEAP$1_old i.0$2_0_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool9$1_0 (distinct 1 0)))
            (=>
               tobool9$1_0
               (let
                  ((spanp.0$1_0 incdec.ptr1$1_0))
                  (let
                     ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                      (_$1_2 (select HEAP$1 spanp.0$1_0)))
                     (let
                        ((conv2$1_0 _$1_2)
                         (conv3$1_0 _$1_1))
                        (let
                           ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                           (=>
                              (not cmp$1_0)
                              (let
                                 ((conv5$1_0 _$1_2))
                                 (let
                                    ((cmp6$1_0 (distinct conv5$1_0 0)))
                                    (=>
                                       (not cmp6$1_0)
                                       (let
                                          ((p.0$1_0 incdec.ptr$1_0)
                                           (i.0$2_0 i.0$2_0_old))
                                          (let
                                             ((l.0$2_0 l.0$2_0_old)
                                              (reject$2_0 reject$2_0_old)
                                              (s.addr.0$2_0 s.addr.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (inc$2_0 (+ i.0$2_0 1)))
                                             (let
                                                ((i.0$2_0 inc$2_0))
                                                (let
                                                   ((idxprom$2_0 i.0$2_0))
                                                   (let
                                                      ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                      (let
                                                         ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                         (let
                                                            ((tobool2$2_0 (distinct _$2_1 0)))
                                                            (=>
                                                               (not tobool2$2_0)
                                                               (let
                                                                  ((inc10$2_0 (+ l.0$2_0 1))
                                                                   (incdec.ptr$2_0 (+ s.addr.0$2_0 1)))
                                                                  (let
                                                                     ((l.0$2_0 inc10$2_0)
                                                                      (s.addr.0$2_0 incdec.ptr$2_0))
                                                                     (INV_MAIN_0 p.0$1_0 reject$1_0 s$1_0 HEAP$1 l.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2))))))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old reject$1_0_old s$1_0_old HEAP$1_old i.0$2_0_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool9$1_0 (distinct 1 0)))
            (=>
               (not tobool9$1_0)
               (let
                  ((p.0$1_0 incdec.ptr$1_0)
                   (i.0$2_0 i.0$2_0_old))
                  (let
                     ((l.0$2_0 l.0$2_0_old)
                      (reject$2_0 reject$2_0_old)
                      (s.addr.0$2_0 s.addr.0$2_0_old)
                      (HEAP$2 HEAP$2_old)
                      (inc$2_0 (+ i.0$2_0 1)))
                     (let
                        ((i.0$2_0 inc$2_0))
                        (let
                           ((idxprom$2_0 i.0$2_0))
                           (let
                              ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                              (let
                                 ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                 (let
                                    ((tobool2$2_0 (distinct _$2_1 0)))
                                    (=>
                                       (not tobool2$2_0)
                                       (let
                                          ((inc10$2_0 (+ l.0$2_0 1))
                                           (incdec.ptr$2_0 (+ s.addr.0$2_0 1)))
                                          (let
                                             ((l.0$2_0 inc10$2_0)
                                              (s.addr.0$2_0 incdec.ptr$2_0))
                                             (INV_MAIN_0 p.0$1_0 reject$1_0 s$1_0 HEAP$1 l.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old reject$1_0_old s$1_0_old HEAP$1_old i.0$2_0_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool9$1_0 (distinct 1 0)))
            (=>
               tobool9$1_0
               (let
                  ((spanp.0$1_0 incdec.ptr1$1_0))
                  (let
                     ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                      (_$1_2 (select HEAP$1 spanp.0$1_0)))
                     (let
                        ((conv2$1_0 _$1_2)
                         (conv3$1_0 _$1_1))
                        (let
                           ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                           (=>
                              (not cmp$1_0)
                              (let
                                 ((conv5$1_0 _$1_2))
                                 (let
                                    ((cmp6$1_0 (distinct conv5$1_0 0)))
                                    (=>
                                       cmp6$1_0
                                       (let
                                          ((i.0$2_0 i.0$2_0_old))
                                          (let
                                             ((l.0$2_0 l.0$2_0_old)
                                              (reject$2_0 reject$2_0_old)
                                              (s.addr.0$2_0 s.addr.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (inc$2_0 (+ i.0$2_0 1)))
                                             (let
                                                ((i.0$2_0 inc$2_0))
                                                (let
                                                   ((idxprom$2_0 i.0$2_0))
                                                   (let
                                                      ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                      (let
                                                         ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                         (let
                                                            ((tobool2$2_0 (distinct _$2_1 0)))
                                                            (=>
                                                               tobool2$2_0
                                                               (let
                                                                  ((_$2_2 (select HEAP$2 s.addr.0$2_0)))
                                                                  (let
                                                                     ((conv4$2_0 _$2_2)
                                                                      (idxprom5$2_0 i.0$2_0))
                                                                     (let
                                                                        ((arrayidx6$2_0 (+ reject$2_0 idxprom5$2_0)))
                                                                        (let
                                                                           ((_$2_3 (select HEAP$2 arrayidx6$2_0)))
                                                                           (let
                                                                              ((conv7$2_0 _$2_3))
                                                                              (let
                                                                                 ((cmp$2_0 (= conv4$2_0 conv7$2_0)))
                                                                                 (=>
                                                                                    (not cmp$2_0)
                                                                                    (INV_MAIN_1 _$1_1 incdec.ptr$1_0 incdec.ptr1$1_0 reject$1_0 s$1_0 HEAP$1 i.0$2_0 l.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old reject$1_0_old s$1_0_old HEAP$1_old i.0$2_0_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (reject$1_0 reject$1_0_old)
             (s$1_0 s$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool9$1_0 (distinct 1 0)))
            (=>
               tobool9$1_0
               (let
                  ((spanp.0$1_0 incdec.ptr1$1_0))
                  (let
                     ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                      (_$1_2 (select HEAP$1 spanp.0$1_0)))
                     (let
                        ((conv2$1_0 _$1_2)
                         (conv3$1_0 _$1_1))
                        (let
                           ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                           (=>
                              (not cmp$1_0)
                              (let
                                 ((conv5$1_0 _$1_2))
                                 (let
                                    ((cmp6$1_0 (distinct conv5$1_0 0)))
                                    (=>
                                       cmp6$1_0
                                       (=>
                                          (let
                                             ((i.0$2_0 i.0$2_0_old))
                                             (let
                                                ((l.0$2_0 l.0$2_0_old)
                                                 (reject$2_0 reject$2_0_old)
                                                 (s.addr.0$2_0 s.addr.0$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (inc$2_0 (+ i.0$2_0 1)))
                                                (let
                                                   ((i.0$2_0 inc$2_0))
                                                   (let
                                                      ((idxprom$2_0 i.0$2_0))
                                                      (let
                                                         ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                                                         (let
                                                            ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                                                            (let
                                                               ((tobool2$2_0 (distinct _$2_1 0)))
                                                               (=>
                                                                  tobool2$2_0
                                                                  (let
                                                                     ((_$2_2 (select HEAP$2 s.addr.0$2_0)))
                                                                     (let
                                                                        ((conv4$2_0 _$2_2)
                                                                         (idxprom5$2_0 i.0$2_0))
                                                                        (let
                                                                           ((arrayidx6$2_0 (+ reject$2_0 idxprom5$2_0)))
                                                                           (let
                                                                              ((_$2_3 (select HEAP$2 arrayidx6$2_0)))
                                                                              (let
                                                                                 ((conv7$2_0 _$2_3))
                                                                                 (let
                                                                                    ((cmp$2_0 (= conv4$2_0 conv7$2_0)))
                                                                                    (not (not cmp$2_0))))))))))))))))
                                          (INV_MAIN_1 _$1_1 incdec.ptr$1_0 incdec.ptr1$1_0 reject$1_0 s$1_0 HEAP$1 i.0$2_0_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (reject$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (l.0$2_0_old Int)
       (reject$2_0_old Int)
       (s.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old reject$1_0_old s$1_0_old HEAP$1_old i.0$2_0_old l.0$2_0_old reject$2_0_old s.addr.0$2_0_old HEAP$2_old)
         (let
            ((i.0$2_0 i.0$2_0_old))
            (let
               ((l.0$2_0 l.0$2_0_old)
                (reject$2_0 reject$2_0_old)
                (s.addr.0$2_0 s.addr.0$2_0_old)
                (HEAP$2 HEAP$2_old)
                (inc$2_0 (+ i.0$2_0 1)))
               (let
                  ((i.0$2_0 inc$2_0))
                  (let
                     ((idxprom$2_0 i.0$2_0))
                     (let
                        ((arrayidx$2_0 (+ reject$2_0 idxprom$2_0)))
                        (let
                           ((_$2_1 (select HEAP$2 arrayidx$2_0)))
                           (let
                              ((tobool2$2_0 (distinct _$2_1 0)))
                              (=>
                                 tobool2$2_0
                                 (let
                                    ((_$2_2 (select HEAP$2 s.addr.0$2_0)))
                                    (let
                                       ((conv4$2_0 _$2_2)
                                        (idxprom5$2_0 i.0$2_0))
                                       (let
                                          ((arrayidx6$2_0 (+ reject$2_0 idxprom5$2_0)))
                                          (let
                                             ((_$2_3 (select HEAP$2 arrayidx6$2_0)))
                                             (let
                                                ((conv7$2_0 _$2_3))
                                                (let
                                                   ((cmp$2_0 (= conv4$2_0 conv7$2_0)))
                                                   (=>
                                                      (not cmp$2_0)
                                                      (=>
                                                         (let
                                                            ((_$1_1 _$1_1_old)
                                                             (incdec.ptr$1_0 incdec.ptr$1_0_old)
                                                             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
                                                             (reject$1_0 reject$1_0_old)
                                                             (s$1_0 s$1_0_old)
                                                             (HEAP$1 HEAP$1_old)
                                                             (tobool9$1_0 (distinct 1 0)))
                                                            (=>
                                                               tobool9$1_0
                                                               (let
                                                                  ((spanp.0$1_0 incdec.ptr1$1_0))
                                                                  (let
                                                                     ((incdec.ptr1$1_0 (+ spanp.0$1_0 1))
                                                                      (_$1_2 (select HEAP$1 spanp.0$1_0)))
                                                                     (let
                                                                        ((conv2$1_0 _$1_2)
                                                                         (conv3$1_0 _$1_1))
                                                                        (let
                                                                           ((cmp$1_0 (= conv2$1_0 conv3$1_0)))
                                                                           (=>
                                                                              (not cmp$1_0)
                                                                              (let
                                                                                 ((conv5$1_0 _$1_2))
                                                                                 (let
                                                                                    ((cmp6$1_0 (distinct conv5$1_0 0)))
                                                                                    (not cmp6$1_0))))))))))
                                                         (INV_MAIN_1 _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old reject$1_0_old s$1_0_old HEAP$1_old i.0$2_0 l.0$2_0 reject$2_0 s.addr.0$2_0 HEAP$2))))))))))))))))))))
(check-sat)
(get-model)
