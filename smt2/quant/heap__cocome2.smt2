;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((items$1_0 Int)
    (itemCount$1_0 Int)
    (onlineItems$1_0 Int)
    (onlineItemCount$1_0 Int)
    (paidOnline$1_0 Int)
    (HEAP$1 (Array Int Int))
    (items$2_0 Int)
    (itemCount$2_0 Int)
    (onlineItems$2_0 Int)
    (onlineItemCount$2_0 Int)
    (paidOnline$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= items$1_0 items$2_0)
      (= itemCount$1_0 itemCount$2_0)
      (= onlineItems$1_0 onlineItems$2_0)
      (= onlineItemCount$1_0 onlineItemCount$2_0)
      (= paidOnline$1_0 paidOnline$2_0)
      (= onlineItemCount$1_0 0)
      (= paidOnline$1_0 0)
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
; :annot (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 HEAP$1 i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_42
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
      ((items$1_0_old Int)
       (itemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (paidOnline$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (items$2_0_old Int)
       (itemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (paidOnline$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV items$1_0_old itemCount$1_0_old onlineItems$1_0_old onlineItemCount$1_0_old paidOnline$1_0_old HEAP$1_old items$2_0_old itemCount$2_0_old onlineItems$2_0_old onlineItemCount$2_0_old paidOnline$2_0_old HEAP$2_old)
         (let
            ((items$1_0 items$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (onlineItems$1_0 onlineItems$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old)
             (paidOnline$1_0 paidOnline$1_0_old)
             (HEAP$1 HEAP$1_old)
             (sum.0$1_0 0)
             (i.0$1_0 0)
             (j.0$1_0 0)
             (items$2_0 items$2_0_old)
             (itemCount$2_0 itemCount$2_0_old)
             (onlineItems$2_0 onlineItems$2_0_old)
             (onlineItemCount$2_0 onlineItemCount$2_0_old)
             (paidOnline$2_0 paidOnline$2_0_old)
             (HEAP$2 HEAP$2_old)
             (sum.0$2_0 0)
             (i.0$2_0 0))
            (forall
               ((i1 Int)
                (i2 Int))
               (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     (not .cmp1$1_0)
                     (let
                        ((sub$1_0 (- sum.0$1_0 paidOnline$1_0)))
                        (let
                           ((result$1 sub$1_0)
                            (HEAP$1_res HEAP$1)
                            (i.0$2_0 i.0$2_0_old)
                            (itemCount$2_0 itemCount$2_0_old)
                            (items$2_0 items$2_0_old)
                            (onlineItemCount$2_0 onlineItemCount$2_0_old))
                           (let
                              ((onlineItems$2_0 onlineItems$2_0_old)
                               (paidOnline$2_0 paidOnline$2_0_old)
                               (sum.0$2_0 sum.0$2_0_old)
                               (HEAP$2 HEAP$2_old)
                               (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                               (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                              (let
                                 ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                 (=>
                                    (not .cmp1$2_0)
                                    (let
                                       ((sub$2_0 (- sum.0$2_0 paidOnline$2_0)))
                                       (let
                                          ((result$2 sub$2_0)
                                           (HEAP$2_res HEAP$2))
                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                 (let
                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                       (let
                                          ((sum.1$1_0 add$1_0)
                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                          (=>
                                             cmp3$1_0
                                             (let
                                                ((idxprom5$1_0 j.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                   (let
                                                      ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                         (let
                                                            ((sum.2$1_0 add7$1_0)
                                                             (inc$1_0 (+ i.0$1_0 1))
                                                             (inc9$1_0 (+ j.0$1_0 1)))
                                                            (let
                                                               ((sum.0$1_0 sum.2$1_0)
                                                                (i.0$1_0 inc$1_0)
                                                                (j.0$1_0 inc9$1_0)
                                                                (i.0$2_0 i.0$2_0_old)
                                                                (itemCount$2_0 itemCount$2_0_old)
                                                                (items$2_0 items$2_0_old)
                                                                (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                               (let
                                                                  ((onlineItems$2_0 onlineItems$2_0_old)
                                                                   (paidOnline$2_0 paidOnline$2_0_old)
                                                                   (sum.0$2_0 sum.0$2_0_old)
                                                                   (HEAP$2 HEAP$2_old)
                                                                   (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                   (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                  (let
                                                                     ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                     (=>
                                                                        .cmp1$2_0
                                                                        (let
                                                                           ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                           (=>
                                                                              cmp2$2_0
                                                                              (let
                                                                                 ((idxprom$2_0 i.0$2_0))
                                                                                 (let
                                                                                    ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                                    (let
                                                                                       ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                                       (let
                                                                                          ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                                          (let
                                                                                             ((sum.1$2_0 add$2_0)
                                                                                              (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                             (=>
                                                                                                cmp3$2_0
                                                                                                (let
                                                                                                   ((idxprom5$2_0 i.0$2_0))
                                                                                                   (let
                                                                                                      ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                                                      (let
                                                                                                         ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                                         (let
                                                                                                            ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                                            (let
                                                                                                               ((sum.2$2_0 add7$2_0)
                                                                                                                (inc$2_0 (+ i.0$2_0 1)))
                                                                                                               (let
                                                                                                                  ((sum.0$2_0 sum.2$2_0)
                                                                                                                   (i.0$2_0 inc$2_0))
                                                                                                                  (forall
                                                                                                                     ((i1 Int)
                                                                                                                      (i2 Int))
                                                                                                                     (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                 (let
                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                       (let
                                          ((sum.1$1_0 add$1_0)
                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                          (=>
                                             cmp3$1_0
                                             (let
                                                ((idxprom5$1_0 j.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                   (let
                                                      ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                         (let
                                                            ((sum.2$1_0 add7$1_0)
                                                             (inc$1_0 (+ i.0$1_0 1))
                                                             (inc9$1_0 (+ j.0$1_0 1)))
                                                            (let
                                                               ((sum.0$1_0 sum.2$1_0)
                                                                (i.0$1_0 inc$1_0)
                                                                (j.0$1_0 inc9$1_0)
                                                                (i.0$2_0 i.0$2_0_old)
                                                                (itemCount$2_0 itemCount$2_0_old)
                                                                (items$2_0 items$2_0_old)
                                                                (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                               (let
                                                                  ((onlineItems$2_0 onlineItems$2_0_old)
                                                                   (paidOnline$2_0 paidOnline$2_0_old)
                                                                   (sum.0$2_0 sum.0$2_0_old)
                                                                   (HEAP$2 HEAP$2_old)
                                                                   (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                   (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                  (let
                                                                     ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                     (=>
                                                                        .cmp1$2_0
                                                                        (let
                                                                           ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                           (=>
                                                                              cmp2$2_0
                                                                              (let
                                                                                 ((idxprom$2_0 i.0$2_0))
                                                                                 (let
                                                                                    ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                                    (let
                                                                                       ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                                       (let
                                                                                          ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                                          (let
                                                                                             ((sum.1$2_0 add$2_0)
                                                                                              (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                             (=>
                                                                                                (not cmp3$2_0)
                                                                                                (let
                                                                                                   ((sum.2$2_0 sum.1$2_0)
                                                                                                    (inc$2_0 (+ i.0$2_0 1)))
                                                                                                   (let
                                                                                                      ((sum.0$2_0 sum.2$2_0)
                                                                                                       (i.0$2_0 inc$2_0))
                                                                                                      (forall
                                                                                                         ((i1 Int)
                                                                                                          (i2 Int))
                                                                                                         (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                 (let
                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                       (let
                                          ((sum.1$1_0 add$1_0)
                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                          (=>
                                             cmp3$1_0
                                             (let
                                                ((idxprom5$1_0 j.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                   (let
                                                      ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                         (let
                                                            ((sum.2$1_0 add7$1_0)
                                                             (inc$1_0 (+ i.0$1_0 1))
                                                             (inc9$1_0 (+ j.0$1_0 1)))
                                                            (let
                                                               ((sum.0$1_0 sum.2$1_0)
                                                                (i.0$1_0 inc$1_0)
                                                                (j.0$1_0 inc9$1_0)
                                                                (i.0$2_0 i.0$2_0_old)
                                                                (itemCount$2_0 itemCount$2_0_old)
                                                                (items$2_0 items$2_0_old)
                                                                (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                               (let
                                                                  ((onlineItems$2_0 onlineItems$2_0_old)
                                                                   (paidOnline$2_0 paidOnline$2_0_old)
                                                                   (sum.0$2_0 sum.0$2_0_old)
                                                                   (HEAP$2 HEAP$2_old)
                                                                   (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                   (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                  (let
                                                                     ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                     (=>
                                                                        .cmp1$2_0
                                                                        (let
                                                                           ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                           (=>
                                                                              (not cmp2$2_0)
                                                                              (let
                                                                                 ((sum.1$2_0 sum.0$2_0)
                                                                                  (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                 (=>
                                                                                    cmp3$2_0
                                                                                    (let
                                                                                       ((idxprom5$2_0 i.0$2_0))
                                                                                       (let
                                                                                          ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                                          (let
                                                                                             ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                             (let
                                                                                                ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                                (let
                                                                                                   ((sum.2$2_0 add7$2_0)
                                                                                                    (inc$2_0 (+ i.0$2_0 1)))
                                                                                                   (let
                                                                                                      ((sum.0$2_0 sum.2$2_0)
                                                                                                       (i.0$2_0 inc$2_0))
                                                                                                      (forall
                                                                                                         ((i1 Int)
                                                                                                          (i2 Int))
                                                                                                         (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                 (let
                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                       (let
                                          ((sum.1$1_0 add$1_0)
                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                          (=>
                                             cmp3$1_0
                                             (let
                                                ((idxprom5$1_0 j.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                   (let
                                                      ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                         (let
                                                            ((sum.2$1_0 add7$1_0)
                                                             (inc$1_0 (+ i.0$1_0 1))
                                                             (inc9$1_0 (+ j.0$1_0 1)))
                                                            (let
                                                               ((sum.0$1_0 sum.2$1_0)
                                                                (i.0$1_0 inc$1_0)
                                                                (j.0$1_0 inc9$1_0)
                                                                (i.0$2_0 i.0$2_0_old)
                                                                (itemCount$2_0 itemCount$2_0_old)
                                                                (items$2_0 items$2_0_old)
                                                                (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                               (let
                                                                  ((onlineItems$2_0 onlineItems$2_0_old)
                                                                   (paidOnline$2_0 paidOnline$2_0_old)
                                                                   (sum.0$2_0 sum.0$2_0_old)
                                                                   (HEAP$2 HEAP$2_old)
                                                                   (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                   (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                  (let
                                                                     ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                     (=>
                                                                        .cmp1$2_0
                                                                        (let
                                                                           ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                           (=>
                                                                              (not cmp2$2_0)
                                                                              (let
                                                                                 ((sum.1$2_0 sum.0$2_0)
                                                                                  (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                 (=>
                                                                                    (not cmp3$2_0)
                                                                                    (let
                                                                                       ((sum.2$2_0 sum.1$2_0)
                                                                                        (inc$2_0 (+ i.0$2_0 1)))
                                                                                       (let
                                                                                          ((sum.0$2_0 sum.2$2_0)
                                                                                           (i.0$2_0 inc$2_0))
                                                                                          (forall
                                                                                             ((i1 Int)
                                                                                              (i2 Int))
                                                                                             (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                 (let
                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                       (let
                                          ((sum.1$1_0 add$1_0)
                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                          (=>
                                             (not cmp3$1_0)
                                             (let
                                                ((sum.2$1_0 sum.1$1_0)
                                                 (inc$1_0 (+ i.0$1_0 1))
                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                (let
                                                   ((sum.0$1_0 sum.2$1_0)
                                                    (i.0$1_0 inc$1_0)
                                                    (j.0$1_0 inc9$1_0)
                                                    (i.0$2_0 i.0$2_0_old)
                                                    (itemCount$2_0 itemCount$2_0_old)
                                                    (items$2_0 items$2_0_old)
                                                    (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                   (let
                                                      ((onlineItems$2_0 onlineItems$2_0_old)
                                                       (paidOnline$2_0 paidOnline$2_0_old)
                                                       (sum.0$2_0 sum.0$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                       (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                      (let
                                                         ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                         (=>
                                                            .cmp1$2_0
                                                            (let
                                                               ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                               (=>
                                                                  cmp2$2_0
                                                                  (let
                                                                     ((idxprom$2_0 i.0$2_0))
                                                                     (let
                                                                        ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                        (let
                                                                           ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                           (let
                                                                              ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                              (let
                                                                                 ((sum.1$2_0 add$2_0)
                                                                                  (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                 (=>
                                                                                    cmp3$2_0
                                                                                    (let
                                                                                       ((idxprom5$2_0 i.0$2_0))
                                                                                       (let
                                                                                          ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                                          (let
                                                                                             ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                             (let
                                                                                                ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                                (let
                                                                                                   ((sum.2$2_0 add7$2_0)
                                                                                                    (inc$2_0 (+ i.0$2_0 1)))
                                                                                                   (let
                                                                                                      ((sum.0$2_0 sum.2$2_0)
                                                                                                       (i.0$2_0 inc$2_0))
                                                                                                      (forall
                                                                                                         ((i1 Int)
                                                                                                          (i2 Int))
                                                                                                         (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                 (let
                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                       (let
                                          ((sum.1$1_0 add$1_0)
                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                          (=>
                                             (not cmp3$1_0)
                                             (let
                                                ((sum.2$1_0 sum.1$1_0)
                                                 (inc$1_0 (+ i.0$1_0 1))
                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                (let
                                                   ((sum.0$1_0 sum.2$1_0)
                                                    (i.0$1_0 inc$1_0)
                                                    (j.0$1_0 inc9$1_0)
                                                    (i.0$2_0 i.0$2_0_old)
                                                    (itemCount$2_0 itemCount$2_0_old)
                                                    (items$2_0 items$2_0_old)
                                                    (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                   (let
                                                      ((onlineItems$2_0 onlineItems$2_0_old)
                                                       (paidOnline$2_0 paidOnline$2_0_old)
                                                       (sum.0$2_0 sum.0$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                       (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                      (let
                                                         ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                         (=>
                                                            .cmp1$2_0
                                                            (let
                                                               ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                               (=>
                                                                  cmp2$2_0
                                                                  (let
                                                                     ((idxprom$2_0 i.0$2_0))
                                                                     (let
                                                                        ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                        (let
                                                                           ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                           (let
                                                                              ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                              (let
                                                                                 ((sum.1$2_0 add$2_0)
                                                                                  (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                 (=>
                                                                                    (not cmp3$2_0)
                                                                                    (let
                                                                                       ((sum.2$2_0 sum.1$2_0)
                                                                                        (inc$2_0 (+ i.0$2_0 1)))
                                                                                       (let
                                                                                          ((sum.0$2_0 sum.2$2_0)
                                                                                           (i.0$2_0 inc$2_0))
                                                                                          (forall
                                                                                             ((i1 Int)
                                                                                              (i2 Int))
                                                                                             (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                 (let
                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                       (let
                                          ((sum.1$1_0 add$1_0)
                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                          (=>
                                             (not cmp3$1_0)
                                             (let
                                                ((sum.2$1_0 sum.1$1_0)
                                                 (inc$1_0 (+ i.0$1_0 1))
                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                (let
                                                   ((sum.0$1_0 sum.2$1_0)
                                                    (i.0$1_0 inc$1_0)
                                                    (j.0$1_0 inc9$1_0)
                                                    (i.0$2_0 i.0$2_0_old)
                                                    (itemCount$2_0 itemCount$2_0_old)
                                                    (items$2_0 items$2_0_old)
                                                    (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                   (let
                                                      ((onlineItems$2_0 onlineItems$2_0_old)
                                                       (paidOnline$2_0 paidOnline$2_0_old)
                                                       (sum.0$2_0 sum.0$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                       (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                      (let
                                                         ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                         (=>
                                                            .cmp1$2_0
                                                            (let
                                                               ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                               (=>
                                                                  (not cmp2$2_0)
                                                                  (let
                                                                     ((sum.1$2_0 sum.0$2_0)
                                                                      (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                     (=>
                                                                        cmp3$2_0
                                                                        (let
                                                                           ((idxprom5$2_0 i.0$2_0))
                                                                           (let
                                                                              ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                              (let
                                                                                 ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                 (let
                                                                                    ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                    (let
                                                                                       ((sum.2$2_0 add7$2_0)
                                                                                        (inc$2_0 (+ i.0$2_0 1)))
                                                                                       (let
                                                                                          ((sum.0$2_0 sum.2$2_0)
                                                                                           (i.0$2_0 inc$2_0))
                                                                                          (forall
                                                                                             ((i1 Int)
                                                                                              (i2 Int))
                                                                                             (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                 (let
                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                       (let
                                          ((sum.1$1_0 add$1_0)
                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                          (=>
                                             (not cmp3$1_0)
                                             (let
                                                ((sum.2$1_0 sum.1$1_0)
                                                 (inc$1_0 (+ i.0$1_0 1))
                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                (let
                                                   ((sum.0$1_0 sum.2$1_0)
                                                    (i.0$1_0 inc$1_0)
                                                    (j.0$1_0 inc9$1_0)
                                                    (i.0$2_0 i.0$2_0_old)
                                                    (itemCount$2_0 itemCount$2_0_old)
                                                    (items$2_0 items$2_0_old)
                                                    (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                   (let
                                                      ((onlineItems$2_0 onlineItems$2_0_old)
                                                       (paidOnline$2_0 paidOnline$2_0_old)
                                                       (sum.0$2_0 sum.0$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                       (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                      (let
                                                         ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                         (=>
                                                            .cmp1$2_0
                                                            (let
                                                               ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                               (=>
                                                                  (not cmp2$2_0)
                                                                  (let
                                                                     ((sum.1$2_0 sum.0$2_0)
                                                                      (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                     (=>
                                                                        (not cmp3$2_0)
                                                                        (let
                                                                           ((sum.2$2_0 sum.1$2_0)
                                                                            (inc$2_0 (+ i.0$2_0 1)))
                                                                           (let
                                                                              ((sum.0$2_0 sum.2$2_0)
                                                                               (i.0$2_0 inc$2_0))
                                                                              (forall
                                                                                 ((i1 Int)
                                                                                  (i2 Int))
                                                                                 (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sum.1$1_0 sum.0$1_0)
                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                              (=>
                                 cmp3$1_0
                                 (let
                                    ((idxprom5$1_0 j.0$1_0))
                                    (let
                                       ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                       (let
                                          ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                          (let
                                             ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                             (let
                                                ((sum.2$1_0 add7$1_0)
                                                 (inc$1_0 (+ i.0$1_0 1))
                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                (let
                                                   ((sum.0$1_0 sum.2$1_0)
                                                    (i.0$1_0 inc$1_0)
                                                    (j.0$1_0 inc9$1_0)
                                                    (i.0$2_0 i.0$2_0_old)
                                                    (itemCount$2_0 itemCount$2_0_old)
                                                    (items$2_0 items$2_0_old)
                                                    (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                   (let
                                                      ((onlineItems$2_0 onlineItems$2_0_old)
                                                       (paidOnline$2_0 paidOnline$2_0_old)
                                                       (sum.0$2_0 sum.0$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                       (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                      (let
                                                         ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                         (=>
                                                            .cmp1$2_0
                                                            (let
                                                               ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                               (=>
                                                                  cmp2$2_0
                                                                  (let
                                                                     ((idxprom$2_0 i.0$2_0))
                                                                     (let
                                                                        ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                        (let
                                                                           ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                           (let
                                                                              ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                              (let
                                                                                 ((sum.1$2_0 add$2_0)
                                                                                  (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                 (=>
                                                                                    cmp3$2_0
                                                                                    (let
                                                                                       ((idxprom5$2_0 i.0$2_0))
                                                                                       (let
                                                                                          ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                                          (let
                                                                                             ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                             (let
                                                                                                ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                                (let
                                                                                                   ((sum.2$2_0 add7$2_0)
                                                                                                    (inc$2_0 (+ i.0$2_0 1)))
                                                                                                   (let
                                                                                                      ((sum.0$2_0 sum.2$2_0)
                                                                                                       (i.0$2_0 inc$2_0))
                                                                                                      (forall
                                                                                                         ((i1 Int)
                                                                                                          (i2 Int))
                                                                                                         (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sum.1$1_0 sum.0$1_0)
                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                              (=>
                                 cmp3$1_0
                                 (let
                                    ((idxprom5$1_0 j.0$1_0))
                                    (let
                                       ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                       (let
                                          ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                          (let
                                             ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                             (let
                                                ((sum.2$1_0 add7$1_0)
                                                 (inc$1_0 (+ i.0$1_0 1))
                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                (let
                                                   ((sum.0$1_0 sum.2$1_0)
                                                    (i.0$1_0 inc$1_0)
                                                    (j.0$1_0 inc9$1_0)
                                                    (i.0$2_0 i.0$2_0_old)
                                                    (itemCount$2_0 itemCount$2_0_old)
                                                    (items$2_0 items$2_0_old)
                                                    (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                   (let
                                                      ((onlineItems$2_0 onlineItems$2_0_old)
                                                       (paidOnline$2_0 paidOnline$2_0_old)
                                                       (sum.0$2_0 sum.0$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                       (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                      (let
                                                         ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                         (=>
                                                            .cmp1$2_0
                                                            (let
                                                               ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                               (=>
                                                                  cmp2$2_0
                                                                  (let
                                                                     ((idxprom$2_0 i.0$2_0))
                                                                     (let
                                                                        ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                        (let
                                                                           ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                           (let
                                                                              ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                              (let
                                                                                 ((sum.1$2_0 add$2_0)
                                                                                  (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                 (=>
                                                                                    (not cmp3$2_0)
                                                                                    (let
                                                                                       ((sum.2$2_0 sum.1$2_0)
                                                                                        (inc$2_0 (+ i.0$2_0 1)))
                                                                                       (let
                                                                                          ((sum.0$2_0 sum.2$2_0)
                                                                                           (i.0$2_0 inc$2_0))
                                                                                          (forall
                                                                                             ((i1 Int)
                                                                                              (i2 Int))
                                                                                             (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sum.1$1_0 sum.0$1_0)
                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                              (=>
                                 cmp3$1_0
                                 (let
                                    ((idxprom5$1_0 j.0$1_0))
                                    (let
                                       ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                       (let
                                          ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                          (let
                                             ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                             (let
                                                ((sum.2$1_0 add7$1_0)
                                                 (inc$1_0 (+ i.0$1_0 1))
                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                (let
                                                   ((sum.0$1_0 sum.2$1_0)
                                                    (i.0$1_0 inc$1_0)
                                                    (j.0$1_0 inc9$1_0)
                                                    (i.0$2_0 i.0$2_0_old)
                                                    (itemCount$2_0 itemCount$2_0_old)
                                                    (items$2_0 items$2_0_old)
                                                    (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                   (let
                                                      ((onlineItems$2_0 onlineItems$2_0_old)
                                                       (paidOnline$2_0 paidOnline$2_0_old)
                                                       (sum.0$2_0 sum.0$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                       (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                      (let
                                                         ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                         (=>
                                                            .cmp1$2_0
                                                            (let
                                                               ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                               (=>
                                                                  (not cmp2$2_0)
                                                                  (let
                                                                     ((sum.1$2_0 sum.0$2_0)
                                                                      (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                     (=>
                                                                        cmp3$2_0
                                                                        (let
                                                                           ((idxprom5$2_0 i.0$2_0))
                                                                           (let
                                                                              ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                              (let
                                                                                 ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                 (let
                                                                                    ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                    (let
                                                                                       ((sum.2$2_0 add7$2_0)
                                                                                        (inc$2_0 (+ i.0$2_0 1)))
                                                                                       (let
                                                                                          ((sum.0$2_0 sum.2$2_0)
                                                                                           (i.0$2_0 inc$2_0))
                                                                                          (forall
                                                                                             ((i1 Int)
                                                                                              (i2 Int))
                                                                                             (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sum.1$1_0 sum.0$1_0)
                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                              (=>
                                 cmp3$1_0
                                 (let
                                    ((idxprom5$1_0 j.0$1_0))
                                    (let
                                       ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                       (let
                                          ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                          (let
                                             ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                             (let
                                                ((sum.2$1_0 add7$1_0)
                                                 (inc$1_0 (+ i.0$1_0 1))
                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                (let
                                                   ((sum.0$1_0 sum.2$1_0)
                                                    (i.0$1_0 inc$1_0)
                                                    (j.0$1_0 inc9$1_0)
                                                    (i.0$2_0 i.0$2_0_old)
                                                    (itemCount$2_0 itemCount$2_0_old)
                                                    (items$2_0 items$2_0_old)
                                                    (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                   (let
                                                      ((onlineItems$2_0 onlineItems$2_0_old)
                                                       (paidOnline$2_0 paidOnline$2_0_old)
                                                       (sum.0$2_0 sum.0$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                       (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                      (let
                                                         ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                         (=>
                                                            .cmp1$2_0
                                                            (let
                                                               ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                               (=>
                                                                  (not cmp2$2_0)
                                                                  (let
                                                                     ((sum.1$2_0 sum.0$2_0)
                                                                      (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                     (=>
                                                                        (not cmp3$2_0)
                                                                        (let
                                                                           ((sum.2$2_0 sum.1$2_0)
                                                                            (inc$2_0 (+ i.0$2_0 1)))
                                                                           (let
                                                                              ((sum.0$2_0 sum.2$2_0)
                                                                               (i.0$2_0 inc$2_0))
                                                                              (forall
                                                                                 ((i1 Int)
                                                                                  (i2 Int))
                                                                                 (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sum.1$1_0 sum.0$1_0)
                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                              (=>
                                 (not cmp3$1_0)
                                 (let
                                    ((sum.2$1_0 sum.1$1_0)
                                     (inc$1_0 (+ i.0$1_0 1))
                                     (inc9$1_0 (+ j.0$1_0 1)))
                                    (let
                                       ((sum.0$1_0 sum.2$1_0)
                                        (i.0$1_0 inc$1_0)
                                        (j.0$1_0 inc9$1_0)
                                        (i.0$2_0 i.0$2_0_old)
                                        (itemCount$2_0 itemCount$2_0_old)
                                        (items$2_0 items$2_0_old)
                                        (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                       (let
                                          ((onlineItems$2_0 onlineItems$2_0_old)
                                           (paidOnline$2_0 paidOnline$2_0_old)
                                           (sum.0$2_0 sum.0$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                           (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                          (let
                                             ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                             (=>
                                                .cmp1$2_0
                                                (let
                                                   ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                   (=>
                                                      cmp2$2_0
                                                      (let
                                                         ((idxprom$2_0 i.0$2_0))
                                                         (let
                                                            ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                            (let
                                                               ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                               (let
                                                                  ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                  (let
                                                                     ((sum.1$2_0 add$2_0)
                                                                      (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                     (=>
                                                                        cmp3$2_0
                                                                        (let
                                                                           ((idxprom5$2_0 i.0$2_0))
                                                                           (let
                                                                              ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                              (let
                                                                                 ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                 (let
                                                                                    ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                    (let
                                                                                       ((sum.2$2_0 add7$2_0)
                                                                                        (inc$2_0 (+ i.0$2_0 1)))
                                                                                       (let
                                                                                          ((sum.0$2_0 sum.2$2_0)
                                                                                           (i.0$2_0 inc$2_0))
                                                                                          (forall
                                                                                             ((i1 Int)
                                                                                              (i2 Int))
                                                                                             (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sum.1$1_0 sum.0$1_0)
                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                              (=>
                                 (not cmp3$1_0)
                                 (let
                                    ((sum.2$1_0 sum.1$1_0)
                                     (inc$1_0 (+ i.0$1_0 1))
                                     (inc9$1_0 (+ j.0$1_0 1)))
                                    (let
                                       ((sum.0$1_0 sum.2$1_0)
                                        (i.0$1_0 inc$1_0)
                                        (j.0$1_0 inc9$1_0)
                                        (i.0$2_0 i.0$2_0_old)
                                        (itemCount$2_0 itemCount$2_0_old)
                                        (items$2_0 items$2_0_old)
                                        (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                       (let
                                          ((onlineItems$2_0 onlineItems$2_0_old)
                                           (paidOnline$2_0 paidOnline$2_0_old)
                                           (sum.0$2_0 sum.0$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                           (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                          (let
                                             ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                             (=>
                                                .cmp1$2_0
                                                (let
                                                   ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                   (=>
                                                      cmp2$2_0
                                                      (let
                                                         ((idxprom$2_0 i.0$2_0))
                                                         (let
                                                            ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                            (let
                                                               ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                               (let
                                                                  ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                  (let
                                                                     ((sum.1$2_0 add$2_0)
                                                                      (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                     (=>
                                                                        (not cmp3$2_0)
                                                                        (let
                                                                           ((sum.2$2_0 sum.1$2_0)
                                                                            (inc$2_0 (+ i.0$2_0 1)))
                                                                           (let
                                                                              ((sum.0$2_0 sum.2$2_0)
                                                                               (i.0$2_0 inc$2_0))
                                                                              (forall
                                                                                 ((i1 Int)
                                                                                  (i2 Int))
                                                                                 (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sum.1$1_0 sum.0$1_0)
                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                              (=>
                                 (not cmp3$1_0)
                                 (let
                                    ((sum.2$1_0 sum.1$1_0)
                                     (inc$1_0 (+ i.0$1_0 1))
                                     (inc9$1_0 (+ j.0$1_0 1)))
                                    (let
                                       ((sum.0$1_0 sum.2$1_0)
                                        (i.0$1_0 inc$1_0)
                                        (j.0$1_0 inc9$1_0)
                                        (i.0$2_0 i.0$2_0_old)
                                        (itemCount$2_0 itemCount$2_0_old)
                                        (items$2_0 items$2_0_old)
                                        (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                       (let
                                          ((onlineItems$2_0 onlineItems$2_0_old)
                                           (paidOnline$2_0 paidOnline$2_0_old)
                                           (sum.0$2_0 sum.0$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                           (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                          (let
                                             ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                             (=>
                                                .cmp1$2_0
                                                (let
                                                   ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                   (=>
                                                      (not cmp2$2_0)
                                                      (let
                                                         ((sum.1$2_0 sum.0$2_0)
                                                          (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                         (=>
                                                            cmp3$2_0
                                                            (let
                                                               ((idxprom5$2_0 i.0$2_0))
                                                               (let
                                                                  ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                  (let
                                                                     ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                     (let
                                                                        ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                        (let
                                                                           ((sum.2$2_0 add7$2_0)
                                                                            (inc$2_0 (+ i.0$2_0 1)))
                                                                           (let
                                                                              ((sum.0$2_0 sum.2$2_0)
                                                                               (i.0$2_0 inc$2_0))
                                                                              (forall
                                                                                 ((i1 Int)
                                                                                  (i2 Int))
                                                                                 (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sum.1$1_0 sum.0$1_0)
                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                              (=>
                                 (not cmp3$1_0)
                                 (let
                                    ((sum.2$1_0 sum.1$1_0)
                                     (inc$1_0 (+ i.0$1_0 1))
                                     (inc9$1_0 (+ j.0$1_0 1)))
                                    (let
                                       ((sum.0$1_0 sum.2$1_0)
                                        (i.0$1_0 inc$1_0)
                                        (j.0$1_0 inc9$1_0)
                                        (i.0$2_0 i.0$2_0_old)
                                        (itemCount$2_0 itemCount$2_0_old)
                                        (items$2_0 items$2_0_old)
                                        (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                       (let
                                          ((onlineItems$2_0 onlineItems$2_0_old)
                                           (paidOnline$2_0 paidOnline$2_0_old)
                                           (sum.0$2_0 sum.0$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                           (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                          (let
                                             ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                             (=>
                                                .cmp1$2_0
                                                (let
                                                   ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                   (=>
                                                      (not cmp2$2_0)
                                                      (let
                                                         ((sum.1$2_0 sum.0$2_0)
                                                          (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                         (=>
                                                            (not cmp3$2_0)
                                                            (let
                                                               ((sum.2$2_0 sum.1$2_0)
                                                                (inc$2_0 (+ i.0$2_0 1)))
                                                               (let
                                                                  ((sum.0$2_0 sum.2$2_0)
                                                                   (i.0$2_0 inc$2_0))
                                                                  (forall
                                                                     ((i1 Int)
                                                                      (i2 Int))
                                                                     (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                 (let
                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                       (let
                                          ((sum.1$1_0 add$1_0)
                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                          (=>
                                             cmp3$1_0
                                             (let
                                                ((idxprom5$1_0 j.0$1_0))
                                                (let
                                                   ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                   (let
                                                      ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                      (let
                                                         ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                         (let
                                                            ((sum.2$1_0 add7$1_0)
                                                             (inc$1_0 (+ i.0$1_0 1))
                                                             (inc9$1_0 (+ j.0$1_0 1)))
                                                            (let
                                                               ((sum.0$1_0 sum.2$1_0)
                                                                (i.0$1_0 inc$1_0)
                                                                (j.0$1_0 inc9$1_0))
                                                               (=>
                                                                  (and
                                                                     (let
                                                                        ((i.0$2_0 i.0$2_0_old)
                                                                         (itemCount$2_0 itemCount$2_0_old)
                                                                         (items$2_0 items$2_0_old)
                                                                         (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                                        (let
                                                                           ((onlineItems$2_0 onlineItems$2_0_old)
                                                                            (paidOnline$2_0 paidOnline$2_0_old)
                                                                            (sum.0$2_0 sum.0$2_0_old)
                                                                            (HEAP$2 HEAP$2_old)
                                                                            (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                            (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                           (let
                                                                              ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                              (=>
                                                                                 .cmp1$2_0
                                                                                 (let
                                                                                    ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                                    (=>
                                                                                       cmp2$2_0
                                                                                       (let
                                                                                          ((idxprom$2_0 i.0$2_0))
                                                                                          (let
                                                                                             ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                                             (let
                                                                                                ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                                                (let
                                                                                                   ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                                                   (let
                                                                                                      ((sum.1$2_0 add$2_0)
                                                                                                       (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                                      (=>
                                                                                                         cmp3$2_0
                                                                                                         (let
                                                                                                            ((idxprom5$2_0 i.0$2_0))
                                                                                                            (let
                                                                                                               ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                                                               (let
                                                                                                                  ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                                                  (let
                                                                                                                     ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                                                     (let
                                                                                                                        ((sum.2$2_0 add7$2_0)
                                                                                                                         (inc$2_0 (+ i.0$2_0 1)))
                                                                                                                        (let
                                                                                                                           ((sum.0$2_0 sum.2$2_0)
                                                                                                                            (i.0$2_0 inc$2_0))
                                                                                                                           false))))))))))))))))))
                                                                     (let
                                                                        ((i.0$2_0 i.0$2_0_old)
                                                                         (itemCount$2_0 itemCount$2_0_old)
                                                                         (items$2_0 items$2_0_old)
                                                                         (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                                        (let
                                                                           ((onlineItems$2_0 onlineItems$2_0_old)
                                                                            (paidOnline$2_0 paidOnline$2_0_old)
                                                                            (sum.0$2_0 sum.0$2_0_old)
                                                                            (HEAP$2 HEAP$2_old)
                                                                            (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                            (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                           (let
                                                                              ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                              (=>
                                                                                 .cmp1$2_0
                                                                                 (let
                                                                                    ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                                    (=>
                                                                                       cmp2$2_0
                                                                                       (let
                                                                                          ((idxprom$2_0 i.0$2_0))
                                                                                          (let
                                                                                             ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                                             (let
                                                                                                ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                                                (let
                                                                                                   ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                                                   (let
                                                                                                      ((sum.1$2_0 add$2_0)
                                                                                                       (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                                      (=>
                                                                                                         (not cmp3$2_0)
                                                                                                         (let
                                                                                                            ((sum.2$2_0 sum.1$2_0)
                                                                                                             (inc$2_0 (+ i.0$2_0 1)))
                                                                                                            (let
                                                                                                               ((sum.0$2_0 sum.2$2_0)
                                                                                                                (i.0$2_0 inc$2_0))
                                                                                                               false))))))))))))))
                                                                     (let
                                                                        ((i.0$2_0 i.0$2_0_old)
                                                                         (itemCount$2_0 itemCount$2_0_old)
                                                                         (items$2_0 items$2_0_old)
                                                                         (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                                        (let
                                                                           ((onlineItems$2_0 onlineItems$2_0_old)
                                                                            (paidOnline$2_0 paidOnline$2_0_old)
                                                                            (sum.0$2_0 sum.0$2_0_old)
                                                                            (HEAP$2 HEAP$2_old)
                                                                            (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                            (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                           (let
                                                                              ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                              (=>
                                                                                 .cmp1$2_0
                                                                                 (let
                                                                                    ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                                    (=>
                                                                                       (not cmp2$2_0)
                                                                                       (let
                                                                                          ((sum.1$2_0 sum.0$2_0)
                                                                                           (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                          (=>
                                                                                             cmp3$2_0
                                                                                             (let
                                                                                                ((idxprom5$2_0 i.0$2_0))
                                                                                                (let
                                                                                                   ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                                                   (let
                                                                                                      ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                                      (let
                                                                                                         ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                                         (let
                                                                                                            ((sum.2$2_0 add7$2_0)
                                                                                                             (inc$2_0 (+ i.0$2_0 1)))
                                                                                                            (let
                                                                                                               ((sum.0$2_0 sum.2$2_0)
                                                                                                                (i.0$2_0 inc$2_0))
                                                                                                               false))))))))))))))
                                                                     (let
                                                                        ((i.0$2_0 i.0$2_0_old)
                                                                         (itemCount$2_0 itemCount$2_0_old)
                                                                         (items$2_0 items$2_0_old)
                                                                         (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                                        (let
                                                                           ((onlineItems$2_0 onlineItems$2_0_old)
                                                                            (paidOnline$2_0 paidOnline$2_0_old)
                                                                            (sum.0$2_0 sum.0$2_0_old)
                                                                            (HEAP$2 HEAP$2_old)
                                                                            (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                            (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                           (let
                                                                              ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                              (=>
                                                                                 .cmp1$2_0
                                                                                 (let
                                                                                    ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                                    (=>
                                                                                       (not cmp2$2_0)
                                                                                       (let
                                                                                          ((sum.1$2_0 sum.0$2_0)
                                                                                           (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                          (=>
                                                                                             (not cmp3$2_0)
                                                                                             (let
                                                                                                ((sum.2$2_0 sum.1$2_0)
                                                                                                 (inc$2_0 (+ i.0$2_0 1)))
                                                                                                (let
                                                                                                   ((sum.0$2_0 sum.2$2_0)
                                                                                                    (i.0$2_0 inc$2_0))
                                                                                                   false)))))))))))
                                                                  (forall
                                                                     ((i1 Int)
                                                                      (i2_old Int))
                                                                     (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((idxprom$1_0 i.0$1_0))
                              (let
                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                 (let
                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                    (let
                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                       (let
                                          ((sum.1$1_0 add$1_0)
                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                          (=>
                                             (not cmp3$1_0)
                                             (let
                                                ((sum.2$1_0 sum.1$1_0)
                                                 (inc$1_0 (+ i.0$1_0 1))
                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                (let
                                                   ((sum.0$1_0 sum.2$1_0)
                                                    (i.0$1_0 inc$1_0)
                                                    (j.0$1_0 inc9$1_0))
                                                   (=>
                                                      (and
                                                         (let
                                                            ((i.0$2_0 i.0$2_0_old)
                                                             (itemCount$2_0 itemCount$2_0_old)
                                                             (items$2_0 items$2_0_old)
                                                             (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                            (let
                                                               ((onlineItems$2_0 onlineItems$2_0_old)
                                                                (paidOnline$2_0 paidOnline$2_0_old)
                                                                (sum.0$2_0 sum.0$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                               (let
                                                                  ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                  (=>
                                                                     .cmp1$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                        (=>
                                                                           cmp2$2_0
                                                                           (let
                                                                              ((idxprom$2_0 i.0$2_0))
                                                                              (let
                                                                                 ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                                 (let
                                                                                    ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                                    (let
                                                                                       ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                                       (let
                                                                                          ((sum.1$2_0 add$2_0)
                                                                                           (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                          (=>
                                                                                             cmp3$2_0
                                                                                             (let
                                                                                                ((idxprom5$2_0 i.0$2_0))
                                                                                                (let
                                                                                                   ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                                                   (let
                                                                                                      ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                                      (let
                                                                                                         ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                                         (let
                                                                                                            ((sum.2$2_0 add7$2_0)
                                                                                                             (inc$2_0 (+ i.0$2_0 1)))
                                                                                                            (let
                                                                                                               ((sum.0$2_0 sum.2$2_0)
                                                                                                                (i.0$2_0 inc$2_0))
                                                                                                               false))))))))))))))))))
                                                         (let
                                                            ((i.0$2_0 i.0$2_0_old)
                                                             (itemCount$2_0 itemCount$2_0_old)
                                                             (items$2_0 items$2_0_old)
                                                             (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                            (let
                                                               ((onlineItems$2_0 onlineItems$2_0_old)
                                                                (paidOnline$2_0 paidOnline$2_0_old)
                                                                (sum.0$2_0 sum.0$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                               (let
                                                                  ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                  (=>
                                                                     .cmp1$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                        (=>
                                                                           cmp2$2_0
                                                                           (let
                                                                              ((idxprom$2_0 i.0$2_0))
                                                                              (let
                                                                                 ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                                 (let
                                                                                    ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                                    (let
                                                                                       ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                                       (let
                                                                                          ((sum.1$2_0 add$2_0)
                                                                                           (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                          (=>
                                                                                             (not cmp3$2_0)
                                                                                             (let
                                                                                                ((sum.2$2_0 sum.1$2_0)
                                                                                                 (inc$2_0 (+ i.0$2_0 1)))
                                                                                                (let
                                                                                                   ((sum.0$2_0 sum.2$2_0)
                                                                                                    (i.0$2_0 inc$2_0))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((i.0$2_0 i.0$2_0_old)
                                                             (itemCount$2_0 itemCount$2_0_old)
                                                             (items$2_0 items$2_0_old)
                                                             (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                            (let
                                                               ((onlineItems$2_0 onlineItems$2_0_old)
                                                                (paidOnline$2_0 paidOnline$2_0_old)
                                                                (sum.0$2_0 sum.0$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                               (let
                                                                  ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                  (=>
                                                                     .cmp1$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                        (=>
                                                                           (not cmp2$2_0)
                                                                           (let
                                                                              ((sum.1$2_0 sum.0$2_0)
                                                                               (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                              (=>
                                                                                 cmp3$2_0
                                                                                 (let
                                                                                    ((idxprom5$2_0 i.0$2_0))
                                                                                    (let
                                                                                       ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                                       (let
                                                                                          ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                          (let
                                                                                             ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                             (let
                                                                                                ((sum.2$2_0 add7$2_0)
                                                                                                 (inc$2_0 (+ i.0$2_0 1)))
                                                                                                (let
                                                                                                   ((sum.0$2_0 sum.2$2_0)
                                                                                                    (i.0$2_0 inc$2_0))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((i.0$2_0 i.0$2_0_old)
                                                             (itemCount$2_0 itemCount$2_0_old)
                                                             (items$2_0 items$2_0_old)
                                                             (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                            (let
                                                               ((onlineItems$2_0 onlineItems$2_0_old)
                                                                (paidOnline$2_0 paidOnline$2_0_old)
                                                                (sum.0$2_0 sum.0$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                               (let
                                                                  ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                  (=>
                                                                     .cmp1$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                        (=>
                                                                           (not cmp2$2_0)
                                                                           (let
                                                                              ((sum.1$2_0 sum.0$2_0)
                                                                               (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                              (=>
                                                                                 (not cmp3$2_0)
                                                                                 (let
                                                                                    ((sum.2$2_0 sum.1$2_0)
                                                                                     (inc$2_0 (+ i.0$2_0 1)))
                                                                                    (let
                                                                                       ((sum.0$2_0 sum.2$2_0)
                                                                                        (i.0$2_0 inc$2_0))
                                                                                       false)))))))))))
                                                      (forall
                                                         ((i1 Int)
                                                          (i2_old Int))
                                                         (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sum.1$1_0 sum.0$1_0)
                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                              (=>
                                 cmp3$1_0
                                 (let
                                    ((idxprom5$1_0 j.0$1_0))
                                    (let
                                       ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                       (let
                                          ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                          (let
                                             ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                             (let
                                                ((sum.2$1_0 add7$1_0)
                                                 (inc$1_0 (+ i.0$1_0 1))
                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                (let
                                                   ((sum.0$1_0 sum.2$1_0)
                                                    (i.0$1_0 inc$1_0)
                                                    (j.0$1_0 inc9$1_0))
                                                   (=>
                                                      (and
                                                         (let
                                                            ((i.0$2_0 i.0$2_0_old)
                                                             (itemCount$2_0 itemCount$2_0_old)
                                                             (items$2_0 items$2_0_old)
                                                             (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                            (let
                                                               ((onlineItems$2_0 onlineItems$2_0_old)
                                                                (paidOnline$2_0 paidOnline$2_0_old)
                                                                (sum.0$2_0 sum.0$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                               (let
                                                                  ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                  (=>
                                                                     .cmp1$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                        (=>
                                                                           cmp2$2_0
                                                                           (let
                                                                              ((idxprom$2_0 i.0$2_0))
                                                                              (let
                                                                                 ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                                 (let
                                                                                    ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                                    (let
                                                                                       ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                                       (let
                                                                                          ((sum.1$2_0 add$2_0)
                                                                                           (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                          (=>
                                                                                             cmp3$2_0
                                                                                             (let
                                                                                                ((idxprom5$2_0 i.0$2_0))
                                                                                                (let
                                                                                                   ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                                                   (let
                                                                                                      ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                                      (let
                                                                                                         ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                                         (let
                                                                                                            ((sum.2$2_0 add7$2_0)
                                                                                                             (inc$2_0 (+ i.0$2_0 1)))
                                                                                                            (let
                                                                                                               ((sum.0$2_0 sum.2$2_0)
                                                                                                                (i.0$2_0 inc$2_0))
                                                                                                               false))))))))))))))))))
                                                         (let
                                                            ((i.0$2_0 i.0$2_0_old)
                                                             (itemCount$2_0 itemCount$2_0_old)
                                                             (items$2_0 items$2_0_old)
                                                             (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                            (let
                                                               ((onlineItems$2_0 onlineItems$2_0_old)
                                                                (paidOnline$2_0 paidOnline$2_0_old)
                                                                (sum.0$2_0 sum.0$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                               (let
                                                                  ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                  (=>
                                                                     .cmp1$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                        (=>
                                                                           cmp2$2_0
                                                                           (let
                                                                              ((idxprom$2_0 i.0$2_0))
                                                                              (let
                                                                                 ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                                 (let
                                                                                    ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                                    (let
                                                                                       ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                                       (let
                                                                                          ((sum.1$2_0 add$2_0)
                                                                                           (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                                          (=>
                                                                                             (not cmp3$2_0)
                                                                                             (let
                                                                                                ((sum.2$2_0 sum.1$2_0)
                                                                                                 (inc$2_0 (+ i.0$2_0 1)))
                                                                                                (let
                                                                                                   ((sum.0$2_0 sum.2$2_0)
                                                                                                    (i.0$2_0 inc$2_0))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((i.0$2_0 i.0$2_0_old)
                                                             (itemCount$2_0 itemCount$2_0_old)
                                                             (items$2_0 items$2_0_old)
                                                             (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                            (let
                                                               ((onlineItems$2_0 onlineItems$2_0_old)
                                                                (paidOnline$2_0 paidOnline$2_0_old)
                                                                (sum.0$2_0 sum.0$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                               (let
                                                                  ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                  (=>
                                                                     .cmp1$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                        (=>
                                                                           (not cmp2$2_0)
                                                                           (let
                                                                              ((sum.1$2_0 sum.0$2_0)
                                                                               (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                              (=>
                                                                                 cmp3$2_0
                                                                                 (let
                                                                                    ((idxprom5$2_0 i.0$2_0))
                                                                                    (let
                                                                                       ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                                       (let
                                                                                          ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                          (let
                                                                                             ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                             (let
                                                                                                ((sum.2$2_0 add7$2_0)
                                                                                                 (inc$2_0 (+ i.0$2_0 1)))
                                                                                                (let
                                                                                                   ((sum.0$2_0 sum.2$2_0)
                                                                                                    (i.0$2_0 inc$2_0))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((i.0$2_0 i.0$2_0_old)
                                                             (itemCount$2_0 itemCount$2_0_old)
                                                             (items$2_0 items$2_0_old)
                                                             (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                            (let
                                                               ((onlineItems$2_0 onlineItems$2_0_old)
                                                                (paidOnline$2_0 paidOnline$2_0_old)
                                                                (sum.0$2_0 sum.0$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                                (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                               (let
                                                                  ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                                  (=>
                                                                     .cmp1$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                                        (=>
                                                                           (not cmp2$2_0)
                                                                           (let
                                                                              ((sum.1$2_0 sum.0$2_0)
                                                                               (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                              (=>
                                                                                 (not cmp3$2_0)
                                                                                 (let
                                                                                    ((sum.2$2_0 sum.1$2_0)
                                                                                     (inc$2_0 (+ i.0$2_0 1)))
                                                                                    (let
                                                                                       ((sum.0$2_0 sum.2$2_0)
                                                                                        (i.0$2_0 inc$2_0))
                                                                                       false)))))))))))
                                                      (forall
                                                         ((i1 Int)
                                                          (i2_old Int))
                                                         (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (itemCount$1_0 itemCount$1_0_old)
             (items$1_0 items$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (onlineItemCount$1_0 onlineItemCount$1_0_old))
            (let
               ((onlineItems$1_0 onlineItems$1_0_old)
                (paidOnline$1_0 paidOnline$1_0_old)
                (sum.0$1_0 sum.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
               (let
                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                  (=>
                     .cmp1$1_0
                     (let
                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sum.1$1_0 sum.0$1_0)
                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                              (=>
                                 (not cmp3$1_0)
                                 (let
                                    ((sum.2$1_0 sum.1$1_0)
                                     (inc$1_0 (+ i.0$1_0 1))
                                     (inc9$1_0 (+ j.0$1_0 1)))
                                    (let
                                       ((sum.0$1_0 sum.2$1_0)
                                        (i.0$1_0 inc$1_0)
                                        (j.0$1_0 inc9$1_0))
                                       (=>
                                          (and
                                             (let
                                                ((i.0$2_0 i.0$2_0_old)
                                                 (itemCount$2_0 itemCount$2_0_old)
                                                 (items$2_0 items$2_0_old)
                                                 (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                (let
                                                   ((onlineItems$2_0 onlineItems$2_0_old)
                                                    (paidOnline$2_0 paidOnline$2_0_old)
                                                    (sum.0$2_0 sum.0$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                    (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                   (let
                                                      ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                      (=>
                                                         .cmp1$2_0
                                                         (let
                                                            ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                            (=>
                                                               cmp2$2_0
                                                               (let
                                                                  ((idxprom$2_0 i.0$2_0))
                                                                  (let
                                                                     ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                     (let
                                                                        ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                        (let
                                                                           ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                           (let
                                                                              ((sum.1$2_0 add$2_0)
                                                                               (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                              (=>
                                                                                 cmp3$2_0
                                                                                 (let
                                                                                    ((idxprom5$2_0 i.0$2_0))
                                                                                    (let
                                                                                       ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                                       (let
                                                                                          ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                                          (let
                                                                                             ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                             (let
                                                                                                ((sum.2$2_0 add7$2_0)
                                                                                                 (inc$2_0 (+ i.0$2_0 1)))
                                                                                                (let
                                                                                                   ((sum.0$2_0 sum.2$2_0)
                                                                                                    (i.0$2_0 inc$2_0))
                                                                                                   false))))))))))))))))))
                                             (let
                                                ((i.0$2_0 i.0$2_0_old)
                                                 (itemCount$2_0 itemCount$2_0_old)
                                                 (items$2_0 items$2_0_old)
                                                 (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                (let
                                                   ((onlineItems$2_0 onlineItems$2_0_old)
                                                    (paidOnline$2_0 paidOnline$2_0_old)
                                                    (sum.0$2_0 sum.0$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                    (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                   (let
                                                      ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                      (=>
                                                         .cmp1$2_0
                                                         (let
                                                            ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                            (=>
                                                               cmp2$2_0
                                                               (let
                                                                  ((idxprom$2_0 i.0$2_0))
                                                                  (let
                                                                     ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                                                     (let
                                                                        ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                        (let
                                                                           ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                                                           (let
                                                                              ((sum.1$2_0 add$2_0)
                                                                               (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                              (=>
                                                                                 (not cmp3$2_0)
                                                                                 (let
                                                                                    ((sum.2$2_0 sum.1$2_0)
                                                                                     (inc$2_0 (+ i.0$2_0 1)))
                                                                                    (let
                                                                                       ((sum.0$2_0 sum.2$2_0)
                                                                                        (i.0$2_0 inc$2_0))
                                                                                       false))))))))))))))
                                             (let
                                                ((i.0$2_0 i.0$2_0_old)
                                                 (itemCount$2_0 itemCount$2_0_old)
                                                 (items$2_0 items$2_0_old)
                                                 (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                (let
                                                   ((onlineItems$2_0 onlineItems$2_0_old)
                                                    (paidOnline$2_0 paidOnline$2_0_old)
                                                    (sum.0$2_0 sum.0$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                    (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                   (let
                                                      ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                      (=>
                                                         .cmp1$2_0
                                                         (let
                                                            ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                            (=>
                                                               (not cmp2$2_0)
                                                               (let
                                                                  ((sum.1$2_0 sum.0$2_0)
                                                                   (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                  (=>
                                                                     cmp3$2_0
                                                                     (let
                                                                        ((idxprom5$2_0 i.0$2_0))
                                                                        (let
                                                                           ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                                           (let
                                                                              ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                                              (let
                                                                                 ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                                                 (let
                                                                                    ((sum.2$2_0 add7$2_0)
                                                                                     (inc$2_0 (+ i.0$2_0 1)))
                                                                                    (let
                                                                                       ((sum.0$2_0 sum.2$2_0)
                                                                                        (i.0$2_0 inc$2_0))
                                                                                       false))))))))))))))
                                             (let
                                                ((i.0$2_0 i.0$2_0_old)
                                                 (itemCount$2_0 itemCount$2_0_old)
                                                 (items$2_0 items$2_0_old)
                                                 (onlineItemCount$2_0 onlineItemCount$2_0_old))
                                                (let
                                                   ((onlineItems$2_0 onlineItems$2_0_old)
                                                    (paidOnline$2_0 paidOnline$2_0_old)
                                                    (sum.0$2_0 sum.0$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                                                    (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                   (let
                                                      ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                                                      (=>
                                                         .cmp1$2_0
                                                         (let
                                                            ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                                                            (=>
                                                               (not cmp2$2_0)
                                                               (let
                                                                  ((sum.1$2_0 sum.0$2_0)
                                                                   (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                                                  (=>
                                                                     (not cmp3$2_0)
                                                                     (let
                                                                        ((sum.2$2_0 sum.1$2_0)
                                                                         (inc$2_0 (+ i.0$2_0 1)))
                                                                        (let
                                                                           ((sum.0$2_0 sum.2$2_0)
                                                                            (i.0$2_0 inc$2_0))
                                                                           false)))))))))))
                                          (forall
                                             ((i1 Int)
                                              (i2_old Int))
                                             (INV_MAIN_42 i.0$1_0 itemCount$1_0 items$1_0 j.0$1_0 onlineItemCount$1_0 onlineItems$1_0 paidOnline$1_0 sum.0$1_0 i1 (select HEAP$1 i1) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$2_0 i.0$2_0_old)
             (itemCount$2_0 itemCount$2_0_old)
             (items$2_0 items$2_0_old)
             (onlineItemCount$2_0 onlineItemCount$2_0_old))
            (let
               ((onlineItems$2_0 onlineItems$2_0_old)
                (paidOnline$2_0 paidOnline$2_0_old)
                (sum.0$2_0 sum.0$2_0_old)
                (HEAP$2 HEAP$2_old)
                (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
               (let
                  ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                  (=>
                     .cmp1$2_0
                     (let
                        ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                        (=>
                           cmp2$2_0
                           (let
                              ((idxprom$2_0 i.0$2_0))
                              (let
                                 ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                 (let
                                    ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                    (let
                                       ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                       (let
                                          ((sum.1$2_0 add$2_0)
                                           (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                          (=>
                                             cmp3$2_0
                                             (let
                                                ((idxprom5$2_0 i.0$2_0))
                                                (let
                                                   ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                                   (let
                                                      ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                                      (let
                                                         ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                                         (let
                                                            ((sum.2$2_0 add7$2_0)
                                                             (inc$2_0 (+ i.0$2_0 1)))
                                                            (let
                                                               ((sum.0$2_0 sum.2$2_0)
                                                                (i.0$2_0 inc$2_0))
                                                               (=>
                                                                  (and
                                                                     (let
                                                                        ((i.0$1_0 i.0$1_0_old)
                                                                         (itemCount$1_0 itemCount$1_0_old)
                                                                         (items$1_0 items$1_0_old)
                                                                         (j.0$1_0 j.0$1_0_old)
                                                                         (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                                        (let
                                                                           ((onlineItems$1_0 onlineItems$1_0_old)
                                                                            (paidOnline$1_0 paidOnline$1_0_old)
                                                                            (sum.0$1_0 sum.0$1_0_old)
                                                                            (HEAP$1 HEAP$1_old)
                                                                            (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                                            (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                           (let
                                                                              ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                                              (=>
                                                                                 .cmp1$1_0
                                                                                 (let
                                                                                    ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                                                    (=>
                                                                                       cmp2$1_0
                                                                                       (let
                                                                                          ((idxprom$1_0 i.0$1_0))
                                                                                          (let
                                                                                             ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                                                                             (let
                                                                                                ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                                                                                (let
                                                                                                   ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                                                                                   (let
                                                                                                      ((sum.1$1_0 add$1_0)
                                                                                                       (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                                                      (=>
                                                                                                         cmp3$1_0
                                                                                                         (let
                                                                                                            ((idxprom5$1_0 j.0$1_0))
                                                                                                            (let
                                                                                                               ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                                                                               (let
                                                                                                                  ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                                                                                  (let
                                                                                                                     ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                                                                                     (let
                                                                                                                        ((sum.2$1_0 add7$1_0)
                                                                                                                         (inc$1_0 (+ i.0$1_0 1))
                                                                                                                         (inc9$1_0 (+ j.0$1_0 1)))
                                                                                                                        (let
                                                                                                                           ((sum.0$1_0 sum.2$1_0)
                                                                                                                            (i.0$1_0 inc$1_0)
                                                                                                                            (j.0$1_0 inc9$1_0))
                                                                                                                           false))))))))))))))))))
                                                                     (let
                                                                        ((i.0$1_0 i.0$1_0_old)
                                                                         (itemCount$1_0 itemCount$1_0_old)
                                                                         (items$1_0 items$1_0_old)
                                                                         (j.0$1_0 j.0$1_0_old)
                                                                         (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                                        (let
                                                                           ((onlineItems$1_0 onlineItems$1_0_old)
                                                                            (paidOnline$1_0 paidOnline$1_0_old)
                                                                            (sum.0$1_0 sum.0$1_0_old)
                                                                            (HEAP$1 HEAP$1_old)
                                                                            (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                                            (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                           (let
                                                                              ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                                              (=>
                                                                                 .cmp1$1_0
                                                                                 (let
                                                                                    ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                                                    (=>
                                                                                       cmp2$1_0
                                                                                       (let
                                                                                          ((idxprom$1_0 i.0$1_0))
                                                                                          (let
                                                                                             ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                                                                             (let
                                                                                                ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                                                                                (let
                                                                                                   ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                                                                                   (let
                                                                                                      ((sum.1$1_0 add$1_0)
                                                                                                       (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                                                      (=>
                                                                                                         (not cmp3$1_0)
                                                                                                         (let
                                                                                                            ((sum.2$1_0 sum.1$1_0)
                                                                                                             (inc$1_0 (+ i.0$1_0 1))
                                                                                                             (inc9$1_0 (+ j.0$1_0 1)))
                                                                                                            (let
                                                                                                               ((sum.0$1_0 sum.2$1_0)
                                                                                                                (i.0$1_0 inc$1_0)
                                                                                                                (j.0$1_0 inc9$1_0))
                                                                                                               false))))))))))))))
                                                                     (let
                                                                        ((i.0$1_0 i.0$1_0_old)
                                                                         (itemCount$1_0 itemCount$1_0_old)
                                                                         (items$1_0 items$1_0_old)
                                                                         (j.0$1_0 j.0$1_0_old)
                                                                         (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                                        (let
                                                                           ((onlineItems$1_0 onlineItems$1_0_old)
                                                                            (paidOnline$1_0 paidOnline$1_0_old)
                                                                            (sum.0$1_0 sum.0$1_0_old)
                                                                            (HEAP$1 HEAP$1_old)
                                                                            (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                                            (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                           (let
                                                                              ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                                              (=>
                                                                                 .cmp1$1_0
                                                                                 (let
                                                                                    ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                                                    (=>
                                                                                       (not cmp2$1_0)
                                                                                       (let
                                                                                          ((sum.1$1_0 sum.0$1_0)
                                                                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                                          (=>
                                                                                             cmp3$1_0
                                                                                             (let
                                                                                                ((idxprom5$1_0 j.0$1_0))
                                                                                                (let
                                                                                                   ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                                                                   (let
                                                                                                      ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                                                                      (let
                                                                                                         ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                                                                         (let
                                                                                                            ((sum.2$1_0 add7$1_0)
                                                                                                             (inc$1_0 (+ i.0$1_0 1))
                                                                                                             (inc9$1_0 (+ j.0$1_0 1)))
                                                                                                            (let
                                                                                                               ((sum.0$1_0 sum.2$1_0)
                                                                                                                (i.0$1_0 inc$1_0)
                                                                                                                (j.0$1_0 inc9$1_0))
                                                                                                               false))))))))))))))
                                                                     (let
                                                                        ((i.0$1_0 i.0$1_0_old)
                                                                         (itemCount$1_0 itemCount$1_0_old)
                                                                         (items$1_0 items$1_0_old)
                                                                         (j.0$1_0 j.0$1_0_old)
                                                                         (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                                        (let
                                                                           ((onlineItems$1_0 onlineItems$1_0_old)
                                                                            (paidOnline$1_0 paidOnline$1_0_old)
                                                                            (sum.0$1_0 sum.0$1_0_old)
                                                                            (HEAP$1 HEAP$1_old)
                                                                            (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                                            (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                           (let
                                                                              ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                                              (=>
                                                                                 .cmp1$1_0
                                                                                 (let
                                                                                    ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                                                    (=>
                                                                                       (not cmp2$1_0)
                                                                                       (let
                                                                                          ((sum.1$1_0 sum.0$1_0)
                                                                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                                          (=>
                                                                                             (not cmp3$1_0)
                                                                                             (let
                                                                                                ((sum.2$1_0 sum.1$1_0)
                                                                                                 (inc$1_0 (+ i.0$1_0 1))
                                                                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                                                                (let
                                                                                                   ((sum.0$1_0 sum.2$1_0)
                                                                                                    (i.0$1_0 inc$1_0)
                                                                                                    (j.0$1_0 inc9$1_0))
                                                                                                   false)))))))))))
                                                                  (forall
                                                                     ((i1_old Int)
                                                                      (i2 Int))
                                                                     (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$2_0 i.0$2_0_old)
             (itemCount$2_0 itemCount$2_0_old)
             (items$2_0 items$2_0_old)
             (onlineItemCount$2_0 onlineItemCount$2_0_old))
            (let
               ((onlineItems$2_0 onlineItems$2_0_old)
                (paidOnline$2_0 paidOnline$2_0_old)
                (sum.0$2_0 sum.0$2_0_old)
                (HEAP$2 HEAP$2_old)
                (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
               (let
                  ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                  (=>
                     .cmp1$2_0
                     (let
                        ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                        (=>
                           cmp2$2_0
                           (let
                              ((idxprom$2_0 i.0$2_0))
                              (let
                                 ((arrayidx$2_0 (+ items$2_0 (* 4 idxprom$2_0))))
                                 (let
                                    ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                    (let
                                       ((add$2_0 (+ sum.0$2_0 _$2_0)))
                                       (let
                                          ((sum.1$2_0 add$2_0)
                                           (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                                          (=>
                                             (not cmp3$2_0)
                                             (let
                                                ((sum.2$2_0 sum.1$2_0)
                                                 (inc$2_0 (+ i.0$2_0 1)))
                                                (let
                                                   ((sum.0$2_0 sum.2$2_0)
                                                    (i.0$2_0 inc$2_0))
                                                   (=>
                                                      (and
                                                         (let
                                                            ((i.0$1_0 i.0$1_0_old)
                                                             (itemCount$1_0 itemCount$1_0_old)
                                                             (items$1_0 items$1_0_old)
                                                             (j.0$1_0 j.0$1_0_old)
                                                             (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                            (let
                                                               ((onlineItems$1_0 onlineItems$1_0_old)
                                                                (paidOnline$1_0 paidOnline$1_0_old)
                                                                (sum.0$1_0 sum.0$1_0_old)
                                                                (HEAP$1 HEAP$1_old)
                                                                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                               (let
                                                                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                                  (=>
                                                                     .cmp1$1_0
                                                                     (let
                                                                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                                        (=>
                                                                           cmp2$1_0
                                                                           (let
                                                                              ((idxprom$1_0 i.0$1_0))
                                                                              (let
                                                                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                                                                 (let
                                                                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                                                                    (let
                                                                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                                                                       (let
                                                                                          ((sum.1$1_0 add$1_0)
                                                                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                                          (=>
                                                                                             cmp3$1_0
                                                                                             (let
                                                                                                ((idxprom5$1_0 j.0$1_0))
                                                                                                (let
                                                                                                   ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                                                                   (let
                                                                                                      ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                                                                      (let
                                                                                                         ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                                                                         (let
                                                                                                            ((sum.2$1_0 add7$1_0)
                                                                                                             (inc$1_0 (+ i.0$1_0 1))
                                                                                                             (inc9$1_0 (+ j.0$1_0 1)))
                                                                                                            (let
                                                                                                               ((sum.0$1_0 sum.2$1_0)
                                                                                                                (i.0$1_0 inc$1_0)
                                                                                                                (j.0$1_0 inc9$1_0))
                                                                                                               false))))))))))))))))))
                                                         (let
                                                            ((i.0$1_0 i.0$1_0_old)
                                                             (itemCount$1_0 itemCount$1_0_old)
                                                             (items$1_0 items$1_0_old)
                                                             (j.0$1_0 j.0$1_0_old)
                                                             (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                            (let
                                                               ((onlineItems$1_0 onlineItems$1_0_old)
                                                                (paidOnline$1_0 paidOnline$1_0_old)
                                                                (sum.0$1_0 sum.0$1_0_old)
                                                                (HEAP$1 HEAP$1_old)
                                                                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                               (let
                                                                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                                  (=>
                                                                     .cmp1$1_0
                                                                     (let
                                                                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                                        (=>
                                                                           cmp2$1_0
                                                                           (let
                                                                              ((idxprom$1_0 i.0$1_0))
                                                                              (let
                                                                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                                                                 (let
                                                                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                                                                    (let
                                                                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                                                                       (let
                                                                                          ((sum.1$1_0 add$1_0)
                                                                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                                          (=>
                                                                                             (not cmp3$1_0)
                                                                                             (let
                                                                                                ((sum.2$1_0 sum.1$1_0)
                                                                                                 (inc$1_0 (+ i.0$1_0 1))
                                                                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                                                                (let
                                                                                                   ((sum.0$1_0 sum.2$1_0)
                                                                                                    (i.0$1_0 inc$1_0)
                                                                                                    (j.0$1_0 inc9$1_0))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((i.0$1_0 i.0$1_0_old)
                                                             (itemCount$1_0 itemCount$1_0_old)
                                                             (items$1_0 items$1_0_old)
                                                             (j.0$1_0 j.0$1_0_old)
                                                             (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                            (let
                                                               ((onlineItems$1_0 onlineItems$1_0_old)
                                                                (paidOnline$1_0 paidOnline$1_0_old)
                                                                (sum.0$1_0 sum.0$1_0_old)
                                                                (HEAP$1 HEAP$1_old)
                                                                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                               (let
                                                                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                                  (=>
                                                                     .cmp1$1_0
                                                                     (let
                                                                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                                        (=>
                                                                           (not cmp2$1_0)
                                                                           (let
                                                                              ((sum.1$1_0 sum.0$1_0)
                                                                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                              (=>
                                                                                 cmp3$1_0
                                                                                 (let
                                                                                    ((idxprom5$1_0 j.0$1_0))
                                                                                    (let
                                                                                       ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                                                       (let
                                                                                          ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                                                          (let
                                                                                             ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                                                             (let
                                                                                                ((sum.2$1_0 add7$1_0)
                                                                                                 (inc$1_0 (+ i.0$1_0 1))
                                                                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                                                                (let
                                                                                                   ((sum.0$1_0 sum.2$1_0)
                                                                                                    (i.0$1_0 inc$1_0)
                                                                                                    (j.0$1_0 inc9$1_0))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((i.0$1_0 i.0$1_0_old)
                                                             (itemCount$1_0 itemCount$1_0_old)
                                                             (items$1_0 items$1_0_old)
                                                             (j.0$1_0 j.0$1_0_old)
                                                             (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                            (let
                                                               ((onlineItems$1_0 onlineItems$1_0_old)
                                                                (paidOnline$1_0 paidOnline$1_0_old)
                                                                (sum.0$1_0 sum.0$1_0_old)
                                                                (HEAP$1 HEAP$1_old)
                                                                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                               (let
                                                                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                                  (=>
                                                                     .cmp1$1_0
                                                                     (let
                                                                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                                        (=>
                                                                           (not cmp2$1_0)
                                                                           (let
                                                                              ((sum.1$1_0 sum.0$1_0)
                                                                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                              (=>
                                                                                 (not cmp3$1_0)
                                                                                 (let
                                                                                    ((sum.2$1_0 sum.1$1_0)
                                                                                     (inc$1_0 (+ i.0$1_0 1))
                                                                                     (inc9$1_0 (+ j.0$1_0 1)))
                                                                                    (let
                                                                                       ((sum.0$1_0 sum.2$1_0)
                                                                                        (i.0$1_0 inc$1_0)
                                                                                        (j.0$1_0 inc9$1_0))
                                                                                       false)))))))))))
                                                      (forall
                                                         ((i1_old Int)
                                                          (i2 Int))
                                                         (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$2_0 i.0$2_0_old)
             (itemCount$2_0 itemCount$2_0_old)
             (items$2_0 items$2_0_old)
             (onlineItemCount$2_0 onlineItemCount$2_0_old))
            (let
               ((onlineItems$2_0 onlineItems$2_0_old)
                (paidOnline$2_0 paidOnline$2_0_old)
                (sum.0$2_0 sum.0$2_0_old)
                (HEAP$2 HEAP$2_old)
                (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
               (let
                  ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                  (=>
                     .cmp1$2_0
                     (let
                        ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                        (=>
                           (not cmp2$2_0)
                           (let
                              ((sum.1$2_0 sum.0$2_0)
                               (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                              (=>
                                 cmp3$2_0
                                 (let
                                    ((idxprom5$2_0 i.0$2_0))
                                    (let
                                       ((arrayidx6$2_0 (+ onlineItems$2_0 (* 4 idxprom5$2_0))))
                                       (let
                                          ((_$2_1 (select HEAP$2 arrayidx6$2_0)))
                                          (let
                                             ((add7$2_0 (+ sum.1$2_0 _$2_1)))
                                             (let
                                                ((sum.2$2_0 add7$2_0)
                                                 (inc$2_0 (+ i.0$2_0 1)))
                                                (let
                                                   ((sum.0$2_0 sum.2$2_0)
                                                    (i.0$2_0 inc$2_0))
                                                   (=>
                                                      (and
                                                         (let
                                                            ((i.0$1_0 i.0$1_0_old)
                                                             (itemCount$1_0 itemCount$1_0_old)
                                                             (items$1_0 items$1_0_old)
                                                             (j.0$1_0 j.0$1_0_old)
                                                             (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                            (let
                                                               ((onlineItems$1_0 onlineItems$1_0_old)
                                                                (paidOnline$1_0 paidOnline$1_0_old)
                                                                (sum.0$1_0 sum.0$1_0_old)
                                                                (HEAP$1 HEAP$1_old)
                                                                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                               (let
                                                                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                                  (=>
                                                                     .cmp1$1_0
                                                                     (let
                                                                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                                        (=>
                                                                           cmp2$1_0
                                                                           (let
                                                                              ((idxprom$1_0 i.0$1_0))
                                                                              (let
                                                                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                                                                 (let
                                                                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                                                                    (let
                                                                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                                                                       (let
                                                                                          ((sum.1$1_0 add$1_0)
                                                                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                                          (=>
                                                                                             cmp3$1_0
                                                                                             (let
                                                                                                ((idxprom5$1_0 j.0$1_0))
                                                                                                (let
                                                                                                   ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                                                                   (let
                                                                                                      ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                                                                      (let
                                                                                                         ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                                                                         (let
                                                                                                            ((sum.2$1_0 add7$1_0)
                                                                                                             (inc$1_0 (+ i.0$1_0 1))
                                                                                                             (inc9$1_0 (+ j.0$1_0 1)))
                                                                                                            (let
                                                                                                               ((sum.0$1_0 sum.2$1_0)
                                                                                                                (i.0$1_0 inc$1_0)
                                                                                                                (j.0$1_0 inc9$1_0))
                                                                                                               false))))))))))))))))))
                                                         (let
                                                            ((i.0$1_0 i.0$1_0_old)
                                                             (itemCount$1_0 itemCount$1_0_old)
                                                             (items$1_0 items$1_0_old)
                                                             (j.0$1_0 j.0$1_0_old)
                                                             (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                            (let
                                                               ((onlineItems$1_0 onlineItems$1_0_old)
                                                                (paidOnline$1_0 paidOnline$1_0_old)
                                                                (sum.0$1_0 sum.0$1_0_old)
                                                                (HEAP$1 HEAP$1_old)
                                                                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                               (let
                                                                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                                  (=>
                                                                     .cmp1$1_0
                                                                     (let
                                                                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                                        (=>
                                                                           cmp2$1_0
                                                                           (let
                                                                              ((idxprom$1_0 i.0$1_0))
                                                                              (let
                                                                                 ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                                                                 (let
                                                                                    ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                                                                    (let
                                                                                       ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                                                                       (let
                                                                                          ((sum.1$1_0 add$1_0)
                                                                                           (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                                          (=>
                                                                                             (not cmp3$1_0)
                                                                                             (let
                                                                                                ((sum.2$1_0 sum.1$1_0)
                                                                                                 (inc$1_0 (+ i.0$1_0 1))
                                                                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                                                                (let
                                                                                                   ((sum.0$1_0 sum.2$1_0)
                                                                                                    (i.0$1_0 inc$1_0)
                                                                                                    (j.0$1_0 inc9$1_0))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((i.0$1_0 i.0$1_0_old)
                                                             (itemCount$1_0 itemCount$1_0_old)
                                                             (items$1_0 items$1_0_old)
                                                             (j.0$1_0 j.0$1_0_old)
                                                             (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                            (let
                                                               ((onlineItems$1_0 onlineItems$1_0_old)
                                                                (paidOnline$1_0 paidOnline$1_0_old)
                                                                (sum.0$1_0 sum.0$1_0_old)
                                                                (HEAP$1 HEAP$1_old)
                                                                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                               (let
                                                                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                                  (=>
                                                                     .cmp1$1_0
                                                                     (let
                                                                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                                        (=>
                                                                           (not cmp2$1_0)
                                                                           (let
                                                                              ((sum.1$1_0 sum.0$1_0)
                                                                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                              (=>
                                                                                 cmp3$1_0
                                                                                 (let
                                                                                    ((idxprom5$1_0 j.0$1_0))
                                                                                    (let
                                                                                       ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                                                       (let
                                                                                          ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                                                          (let
                                                                                             ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                                                             (let
                                                                                                ((sum.2$1_0 add7$1_0)
                                                                                                 (inc$1_0 (+ i.0$1_0 1))
                                                                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                                                                (let
                                                                                                   ((sum.0$1_0 sum.2$1_0)
                                                                                                    (i.0$1_0 inc$1_0)
                                                                                                    (j.0$1_0 inc9$1_0))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((i.0$1_0 i.0$1_0_old)
                                                             (itemCount$1_0 itemCount$1_0_old)
                                                             (items$1_0 items$1_0_old)
                                                             (j.0$1_0 j.0$1_0_old)
                                                             (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                            (let
                                                               ((onlineItems$1_0 onlineItems$1_0_old)
                                                                (paidOnline$1_0 paidOnline$1_0_old)
                                                                (sum.0$1_0 sum.0$1_0_old)
                                                                (HEAP$1 HEAP$1_old)
                                                                (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                                (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                               (let
                                                                  ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                                  (=>
                                                                     .cmp1$1_0
                                                                     (let
                                                                        ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                                        (=>
                                                                           (not cmp2$1_0)
                                                                           (let
                                                                              ((sum.1$1_0 sum.0$1_0)
                                                                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                              (=>
                                                                                 (not cmp3$1_0)
                                                                                 (let
                                                                                    ((sum.2$1_0 sum.1$1_0)
                                                                                     (inc$1_0 (+ i.0$1_0 1))
                                                                                     (inc9$1_0 (+ j.0$1_0 1)))
                                                                                    (let
                                                                                       ((sum.0$1_0 sum.2$1_0)
                                                                                        (i.0$1_0 inc$1_0)
                                                                                        (j.0$1_0 inc9$1_0))
                                                                                       false)))))))))))
                                                      (forall
                                                         ((i1_old Int)
                                                          (i2 Int))
                                                         (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (itemCount$1_0_old Int)
       (items$1_0_old Int)
       (j.0$1_0_old Int)
       (onlineItemCount$1_0_old Int)
       (onlineItems$1_0_old Int)
       (paidOnline$1_0_old Int)
       (sum.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (i.0$2_0_old Int)
       (itemCount$2_0_old Int)
       (items$2_0_old Int)
       (onlineItemCount$2_0_old Int)
       (onlineItems$2_0_old Int)
       (paidOnline$2_0_old Int)
       (sum.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0_old itemCount$2_0_old items$2_0_old onlineItemCount$2_0_old onlineItems$2_0_old paidOnline$2_0_old sum.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$2_0 i.0$2_0_old)
             (itemCount$2_0 itemCount$2_0_old)
             (items$2_0 items$2_0_old)
             (onlineItemCount$2_0 onlineItemCount$2_0_old))
            (let
               ((onlineItems$2_0 onlineItems$2_0_old)
                (paidOnline$2_0 paidOnline$2_0_old)
                (sum.0$2_0 sum.0$2_0_old)
                (HEAP$2 HEAP$2_old)
                (cmp$2_0 (< i.0$2_0 itemCount$2_0))
                (cmp1$2_0 (< i.0$2_0 onlineItemCount$2_0)))
               (let
                  ((.cmp1$2_0 (ite cmp$2_0 true cmp1$2_0)))
                  (=>
                     .cmp1$2_0
                     (let
                        ((cmp2$2_0 (< i.0$2_0 itemCount$2_0)))
                        (=>
                           (not cmp2$2_0)
                           (let
                              ((sum.1$2_0 sum.0$2_0)
                               (cmp3$2_0 (< i.0$2_0 onlineItemCount$2_0)))
                              (=>
                                 (not cmp3$2_0)
                                 (let
                                    ((sum.2$2_0 sum.1$2_0)
                                     (inc$2_0 (+ i.0$2_0 1)))
                                    (let
                                       ((sum.0$2_0 sum.2$2_0)
                                        (i.0$2_0 inc$2_0))
                                       (=>
                                          (and
                                             (let
                                                ((i.0$1_0 i.0$1_0_old)
                                                 (itemCount$1_0 itemCount$1_0_old)
                                                 (items$1_0 items$1_0_old)
                                                 (j.0$1_0 j.0$1_0_old)
                                                 (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                (let
                                                   ((onlineItems$1_0 onlineItems$1_0_old)
                                                    (paidOnline$1_0 paidOnline$1_0_old)
                                                    (sum.0$1_0 sum.0$1_0_old)
                                                    (HEAP$1 HEAP$1_old)
                                                    (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                    (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                   (let
                                                      ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                      (=>
                                                         .cmp1$1_0
                                                         (let
                                                            ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                            (=>
                                                               cmp2$1_0
                                                               (let
                                                                  ((idxprom$1_0 i.0$1_0))
                                                                  (let
                                                                     ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                                                     (let
                                                                        ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                                                        (let
                                                                           ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                                                           (let
                                                                              ((sum.1$1_0 add$1_0)
                                                                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                              (=>
                                                                                 cmp3$1_0
                                                                                 (let
                                                                                    ((idxprom5$1_0 j.0$1_0))
                                                                                    (let
                                                                                       ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                                                       (let
                                                                                          ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                                                          (let
                                                                                             ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                                                             (let
                                                                                                ((sum.2$1_0 add7$1_0)
                                                                                                 (inc$1_0 (+ i.0$1_0 1))
                                                                                                 (inc9$1_0 (+ j.0$1_0 1)))
                                                                                                (let
                                                                                                   ((sum.0$1_0 sum.2$1_0)
                                                                                                    (i.0$1_0 inc$1_0)
                                                                                                    (j.0$1_0 inc9$1_0))
                                                                                                   false))))))))))))))))))
                                             (let
                                                ((i.0$1_0 i.0$1_0_old)
                                                 (itemCount$1_0 itemCount$1_0_old)
                                                 (items$1_0 items$1_0_old)
                                                 (j.0$1_0 j.0$1_0_old)
                                                 (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                (let
                                                   ((onlineItems$1_0 onlineItems$1_0_old)
                                                    (paidOnline$1_0 paidOnline$1_0_old)
                                                    (sum.0$1_0 sum.0$1_0_old)
                                                    (HEAP$1 HEAP$1_old)
                                                    (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                    (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                   (let
                                                      ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                      (=>
                                                         .cmp1$1_0
                                                         (let
                                                            ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                            (=>
                                                               cmp2$1_0
                                                               (let
                                                                  ((idxprom$1_0 i.0$1_0))
                                                                  (let
                                                                     ((arrayidx$1_0 (+ items$1_0 (* 4 idxprom$1_0))))
                                                                     (let
                                                                        ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                                                        (let
                                                                           ((add$1_0 (+ sum.0$1_0 _$1_0)))
                                                                           (let
                                                                              ((sum.1$1_0 add$1_0)
                                                                               (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                              (=>
                                                                                 (not cmp3$1_0)
                                                                                 (let
                                                                                    ((sum.2$1_0 sum.1$1_0)
                                                                                     (inc$1_0 (+ i.0$1_0 1))
                                                                                     (inc9$1_0 (+ j.0$1_0 1)))
                                                                                    (let
                                                                                       ((sum.0$1_0 sum.2$1_0)
                                                                                        (i.0$1_0 inc$1_0)
                                                                                        (j.0$1_0 inc9$1_0))
                                                                                       false))))))))))))))
                                             (let
                                                ((i.0$1_0 i.0$1_0_old)
                                                 (itemCount$1_0 itemCount$1_0_old)
                                                 (items$1_0 items$1_0_old)
                                                 (j.0$1_0 j.0$1_0_old)
                                                 (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                (let
                                                   ((onlineItems$1_0 onlineItems$1_0_old)
                                                    (paidOnline$1_0 paidOnline$1_0_old)
                                                    (sum.0$1_0 sum.0$1_0_old)
                                                    (HEAP$1 HEAP$1_old)
                                                    (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                    (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                   (let
                                                      ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                      (=>
                                                         .cmp1$1_0
                                                         (let
                                                            ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                            (=>
                                                               (not cmp2$1_0)
                                                               (let
                                                                  ((sum.1$1_0 sum.0$1_0)
                                                                   (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                  (=>
                                                                     cmp3$1_0
                                                                     (let
                                                                        ((idxprom5$1_0 j.0$1_0))
                                                                        (let
                                                                           ((arrayidx6$1_0 (+ onlineItems$1_0 (* 4 idxprom5$1_0))))
                                                                           (let
                                                                              ((_$1_1 (select HEAP$1 arrayidx6$1_0)))
                                                                              (let
                                                                                 ((add7$1_0 (+ sum.1$1_0 _$1_1)))
                                                                                 (let
                                                                                    ((sum.2$1_0 add7$1_0)
                                                                                     (inc$1_0 (+ i.0$1_0 1))
                                                                                     (inc9$1_0 (+ j.0$1_0 1)))
                                                                                    (let
                                                                                       ((sum.0$1_0 sum.2$1_0)
                                                                                        (i.0$1_0 inc$1_0)
                                                                                        (j.0$1_0 inc9$1_0))
                                                                                       false))))))))))))))
                                             (let
                                                ((i.0$1_0 i.0$1_0_old)
                                                 (itemCount$1_0 itemCount$1_0_old)
                                                 (items$1_0 items$1_0_old)
                                                 (j.0$1_0 j.0$1_0_old)
                                                 (onlineItemCount$1_0 onlineItemCount$1_0_old))
                                                (let
                                                   ((onlineItems$1_0 onlineItems$1_0_old)
                                                    (paidOnline$1_0 paidOnline$1_0_old)
                                                    (sum.0$1_0 sum.0$1_0_old)
                                                    (HEAP$1 HEAP$1_old)
                                                    (cmp$1_0 (< i.0$1_0 itemCount$1_0))
                                                    (cmp1$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                   (let
                                                      ((.cmp1$1_0 (ite cmp$1_0 true cmp1$1_0)))
                                                      (=>
                                                         .cmp1$1_0
                                                         (let
                                                            ((cmp2$1_0 (< i.0$1_0 itemCount$1_0)))
                                                            (=>
                                                               (not cmp2$1_0)
                                                               (let
                                                                  ((sum.1$1_0 sum.0$1_0)
                                                                   (cmp3$1_0 (< j.0$1_0 onlineItemCount$1_0)))
                                                                  (=>
                                                                     (not cmp3$1_0)
                                                                     (let
                                                                        ((sum.2$1_0 sum.1$1_0)
                                                                         (inc$1_0 (+ i.0$1_0 1))
                                                                         (inc9$1_0 (+ j.0$1_0 1)))
                                                                        (let
                                                                           ((sum.0$1_0 sum.2$1_0)
                                                                            (i.0$1_0 inc$1_0)
                                                                            (j.0$1_0 inc9$1_0))
                                                                           false)))))))))))
                                          (forall
                                             ((i1_old Int)
                                              (i2 Int))
                                             (INV_MAIN_42 i.0$1_0_old itemCount$1_0_old items$1_0_old j.0$1_0_old onlineItemCount$1_0_old onlineItems$1_0_old paidOnline$1_0_old sum.0$1_0_old i1_old (select HEAP$1_old i1_old) i.0$2_0 itemCount$2_0 items$2_0 onlineItemCount$2_0 onlineItems$2_0 paidOnline$2_0 sum.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))
(check-sat)
(get-model)
