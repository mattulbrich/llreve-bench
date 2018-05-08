;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((a$1_0 Int)
    (n$1_0 Int)
    (HEAP$1 (Array Int Int))
    (a$2_0 Int)
    (n$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= a$1_0 a$2_0)
      (= n$1_0 n$2_0)
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
; :annot (INV_MAIN_42 a$1_0 i.0$1_0 max.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 HEAP$2)
(declare-fun
   INV_MAIN_42
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
      ((a$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV a$1_0_old n$1_0_old HEAP$1_old a$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (n$1_0 n$1_0_old)
             (HEAP$1 HEAP$1_old)
             (i.0$1_0 1)
             (max.0$1_0 0)
             (a$2_0 a$2_0_old))
            (let
               ((n$2_0 n$2_0_old)
                (HEAP$2 HEAP$2_old)
                (arrayidx$2_0 (+ a$2_0 (* 4 0))))
               (let
                  ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                  (let
                     ((i.0$2_0 1)
                      (maxv.0$2_0 _$2_0))
                     (INV_MAIN_42 a$1_0 i.0$1_0 max.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 HEAP$2))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (max.0$1_0 max.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 n$1_0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((idxprom5$1_0 max.0$1_0))
                     (let
                        ((arrayidx6$1_0 (+ a$1_0 (* 4 idxprom5$1_0))))
                        (let
                           ((_$1_2 (select HEAP$1 arrayidx6$1_0)))
                           (let
                              ((result$1 _$1_2)
                               (HEAP$1_res HEAP$1)
                               (a$2_0 a$2_0_old)
                               (i.0$2_0 i.0$2_0_old)
                               (maxv.0$2_0 maxv.0$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((HEAP$2 HEAP$2_old)
                                  (cmp$2_0 (< i.0$2_0 n$2_0)))
                                 (=>
                                    (not cmp$2_0)
                                    (let
                                       ((result$2 maxv.0$2_0)
                                        (HEAP$2_res HEAP$2))
                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (max.0$1_0 max.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 n$1_0)))
               (=>
                  cmp$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ a$1_0 (* 4 idxprom$1_0))))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0))
                            (idxprom1$1_0 max.0$1_0))
                           (let
                              ((arrayidx2$1_0 (+ a$1_0 (* 4 idxprom1$1_0))))
                              (let
                                 ((_$1_1 (select HEAP$1 arrayidx2$1_0)))
                                 (let
                                    ((cmp3$1_0 (>= _$1_0 _$1_1)))
                                    (let
                                       ((i.0.max.0$1_0 (ite cmp3$1_0 i.0$1_0 max.0$1_0))
                                        (inc$1_0 (+ i.0$1_0 1)))
                                       (let
                                          ((i.0$1_0 inc$1_0)
                                           (max.0$1_0 i.0.max.0$1_0)
                                           (a$2_0 a$2_0_old)
                                           (i.0$2_0 i.0$2_0_old)
                                           (maxv.0$2_0 maxv.0$2_0_old)
                                           (n$2_0 n$2_0_old))
                                          (let
                                             ((HEAP$2 HEAP$2_old)
                                              (cmp$2_0 (< i.0$2_0 n$2_0)))
                                             (=>
                                                cmp$2_0
                                                (let
                                                   ((idxprom$2_0 i.0$2_0))
                                                   (let
                                                      ((arrayidx1$2_0 (+ a$2_0 (* 4 idxprom$2_0))))
                                                      (let
                                                         ((_$2_1 (select HEAP$2 arrayidx1$2_0)))
                                                         (let
                                                            ((cmp2$2_0 (>= _$2_1 maxv.0$2_0)))
                                                            (=>
                                                               cmp2$2_0
                                                               (let
                                                                  ((idxprom4$2_0 i.0$2_0))
                                                                  (let
                                                                     ((arrayidx5$2_0 (+ a$2_0 (* 4 idxprom4$2_0))))
                                                                     (let
                                                                        ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                        (let
                                                                           ((maxv.1$2_0 _$2_2)
                                                                            (inc$2_0 (+ i.0$2_0 1)))
                                                                           (let
                                                                              ((i.0$2_0 inc$2_0)
                                                                               (maxv.0$2_0 maxv.1$2_0))
                                                                              (INV_MAIN_42 a$1_0 i.0$1_0 max.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 HEAP$2)))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (max.0$1_0 max.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 n$1_0)))
               (=>
                  cmp$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ a$1_0 (* 4 idxprom$1_0))))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0))
                            (idxprom1$1_0 max.0$1_0))
                           (let
                              ((arrayidx2$1_0 (+ a$1_0 (* 4 idxprom1$1_0))))
                              (let
                                 ((_$1_1 (select HEAP$1 arrayidx2$1_0)))
                                 (let
                                    ((cmp3$1_0 (>= _$1_0 _$1_1)))
                                    (let
                                       ((i.0.max.0$1_0 (ite cmp3$1_0 i.0$1_0 max.0$1_0))
                                        (inc$1_0 (+ i.0$1_0 1)))
                                       (let
                                          ((i.0$1_0 inc$1_0)
                                           (max.0$1_0 i.0.max.0$1_0)
                                           (a$2_0 a$2_0_old)
                                           (i.0$2_0 i.0$2_0_old)
                                           (maxv.0$2_0 maxv.0$2_0_old)
                                           (n$2_0 n$2_0_old))
                                          (let
                                             ((HEAP$2 HEAP$2_old)
                                              (cmp$2_0 (< i.0$2_0 n$2_0)))
                                             (=>
                                                cmp$2_0
                                                (let
                                                   ((idxprom$2_0 i.0$2_0))
                                                   (let
                                                      ((arrayidx1$2_0 (+ a$2_0 (* 4 idxprom$2_0))))
                                                      (let
                                                         ((_$2_1 (select HEAP$2 arrayidx1$2_0)))
                                                         (let
                                                            ((cmp2$2_0 (>= _$2_1 maxv.0$2_0)))
                                                            (=>
                                                               (not cmp2$2_0)
                                                               (let
                                                                  ((maxv.1$2_0 maxv.0$2_0)
                                                                   (inc$2_0 (+ i.0$2_0 1)))
                                                                  (let
                                                                     ((i.0$2_0 inc$2_0)
                                                                      (maxv.0$2_0 maxv.1$2_0))
                                                                     (INV_MAIN_42 a$1_0 i.0$1_0 max.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 HEAP$2))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (max.0$1_0 max.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 n$1_0)))
               (=>
                  cmp$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ a$1_0 (* 4 idxprom$1_0))))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0))
                            (idxprom1$1_0 max.0$1_0))
                           (let
                              ((arrayidx2$1_0 (+ a$1_0 (* 4 idxprom1$1_0))))
                              (let
                                 ((_$1_1 (select HEAP$1 arrayidx2$1_0)))
                                 (let
                                    ((cmp3$1_0 (>= _$1_0 _$1_1)))
                                    (let
                                       ((i.0.max.0$1_0 (ite cmp3$1_0 i.0$1_0 max.0$1_0))
                                        (inc$1_0 (+ i.0$1_0 1)))
                                       (let
                                          ((i.0$1_0 inc$1_0)
                                           (max.0$1_0 i.0.max.0$1_0))
                                          (=>
                                             (and
                                                (let
                                                   ((a$2_0 a$2_0_old)
                                                    (i.0$2_0 i.0$2_0_old)
                                                    (maxv.0$2_0 maxv.0$2_0_old)
                                                    (n$2_0 n$2_0_old))
                                                   (let
                                                      ((HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (< i.0$2_0 n$2_0)))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((idxprom$2_0 i.0$2_0))
                                                            (let
                                                               ((arrayidx1$2_0 (+ a$2_0 (* 4 idxprom$2_0))))
                                                               (let
                                                                  ((_$2_1 (select HEAP$2 arrayidx1$2_0)))
                                                                  (let
                                                                     ((cmp2$2_0 (>= _$2_1 maxv.0$2_0)))
                                                                     (=>
                                                                        cmp2$2_0
                                                                        (let
                                                                           ((idxprom4$2_0 i.0$2_0))
                                                                           (let
                                                                              ((arrayidx5$2_0 (+ a$2_0 (* 4 idxprom4$2_0))))
                                                                              (let
                                                                                 ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                 (let
                                                                                    ((maxv.1$2_0 _$2_2)
                                                                                     (inc$2_0 (+ i.0$2_0 1)))
                                                                                    (let
                                                                                       ((i.0$2_0 inc$2_0)
                                                                                        (maxv.0$2_0 maxv.1$2_0))
                                                                                       false)))))))))))))
                                                (let
                                                   ((a$2_0 a$2_0_old)
                                                    (i.0$2_0 i.0$2_0_old)
                                                    (maxv.0$2_0 maxv.0$2_0_old)
                                                    (n$2_0 n$2_0_old))
                                                   (let
                                                      ((HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (< i.0$2_0 n$2_0)))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((idxprom$2_0 i.0$2_0))
                                                            (let
                                                               ((arrayidx1$2_0 (+ a$2_0 (* 4 idxprom$2_0))))
                                                               (let
                                                                  ((_$2_1 (select HEAP$2 arrayidx1$2_0)))
                                                                  (let
                                                                     ((cmp2$2_0 (>= _$2_1 maxv.0$2_0)))
                                                                     (=>
                                                                        (not cmp2$2_0)
                                                                        (let
                                                                           ((maxv.1$2_0 maxv.0$2_0)
                                                                            (inc$2_0 (+ i.0$2_0 1)))
                                                                           (let
                                                                              ((i.0$2_0 inc$2_0)
                                                                               (maxv.0$2_0 maxv.1$2_0))
                                                                              false)))))))))))
                                             (INV_MAIN_42 a$1_0 i.0$1_0 max.0$1_0 n$1_0 HEAP$1 a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old HEAP$2_old))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$2_0 a$2_0_old)
             (i.0$2_0 i.0$2_0_old)
             (maxv.0$2_0 maxv.0$2_0_old)
             (n$2_0 n$2_0_old))
            (let
               ((HEAP$2 HEAP$2_old)
                (cmp$2_0 (< i.0$2_0 n$2_0)))
               (=>
                  cmp$2_0
                  (let
                     ((idxprom$2_0 i.0$2_0))
                     (let
                        ((arrayidx1$2_0 (+ a$2_0 (* 4 idxprom$2_0))))
                        (let
                           ((_$2_1 (select HEAP$2 arrayidx1$2_0)))
                           (let
                              ((cmp2$2_0 (>= _$2_1 maxv.0$2_0)))
                              (=>
                                 cmp2$2_0
                                 (let
                                    ((idxprom4$2_0 i.0$2_0))
                                    (let
                                       ((arrayidx5$2_0 (+ a$2_0 (* 4 idxprom4$2_0))))
                                       (let
                                          ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                          (let
                                             ((maxv.1$2_0 _$2_2)
                                              (inc$2_0 (+ i.0$2_0 1)))
                                             (let
                                                ((i.0$2_0 inc$2_0)
                                                 (maxv.0$2_0 maxv.1$2_0))
                                                (=>
                                                   (let
                                                      ((a$1_0 a$1_0_old)
                                                       (i.0$1_0 i.0$1_0_old)
                                                       (max.0$1_0 max.0$1_0_old)
                                                       (n$1_0 n$1_0_old))
                                                      (let
                                                         ((HEAP$1 HEAP$1_old)
                                                          (cmp$1_0 (< i.0$1_0 n$1_0)))
                                                         (=>
                                                            cmp$1_0
                                                            (let
                                                               ((idxprom$1_0 i.0$1_0))
                                                               (let
                                                                  ((arrayidx$1_0 (+ a$1_0 (* 4 idxprom$1_0))))
                                                                  (let
                                                                     ((_$1_0 (select HEAP$1 arrayidx$1_0))
                                                                      (idxprom1$1_0 max.0$1_0))
                                                                     (let
                                                                        ((arrayidx2$1_0 (+ a$1_0 (* 4 idxprom1$1_0))))
                                                                        (let
                                                                           ((_$1_1 (select HEAP$1 arrayidx2$1_0)))
                                                                           (let
                                                                              ((cmp3$1_0 (>= _$1_0 _$1_1)))
                                                                              (let
                                                                                 ((i.0.max.0$1_0 (ite cmp3$1_0 i.0$1_0 max.0$1_0))
                                                                                  (inc$1_0 (+ i.0$1_0 1)))
                                                                                 (let
                                                                                    ((i.0$1_0 inc$1_0)
                                                                                     (max.0$1_0 i.0.max.0$1_0))
                                                                                    false)))))))))))
                                                   (INV_MAIN_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old HEAP$1_old a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 HEAP$2))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$2_0 a$2_0_old)
             (i.0$2_0 i.0$2_0_old)
             (maxv.0$2_0 maxv.0$2_0_old)
             (n$2_0 n$2_0_old))
            (let
               ((HEAP$2 HEAP$2_old)
                (cmp$2_0 (< i.0$2_0 n$2_0)))
               (=>
                  cmp$2_0
                  (let
                     ((idxprom$2_0 i.0$2_0))
                     (let
                        ((arrayidx1$2_0 (+ a$2_0 (* 4 idxprom$2_0))))
                        (let
                           ((_$2_1 (select HEAP$2 arrayidx1$2_0)))
                           (let
                              ((cmp2$2_0 (>= _$2_1 maxv.0$2_0)))
                              (=>
                                 (not cmp2$2_0)
                                 (let
                                    ((maxv.1$2_0 maxv.0$2_0)
                                     (inc$2_0 (+ i.0$2_0 1)))
                                    (let
                                       ((i.0$2_0 inc$2_0)
                                        (maxv.0$2_0 maxv.1$2_0))
                                       (=>
                                          (let
                                             ((a$1_0 a$1_0_old)
                                              (i.0$1_0 i.0$1_0_old)
                                              (max.0$1_0 max.0$1_0_old)
                                              (n$1_0 n$1_0_old))
                                             (let
                                                ((HEAP$1 HEAP$1_old)
                                                 (cmp$1_0 (< i.0$1_0 n$1_0)))
                                                (=>
                                                   cmp$1_0
                                                   (let
                                                      ((idxprom$1_0 i.0$1_0))
                                                      (let
                                                         ((arrayidx$1_0 (+ a$1_0 (* 4 idxprom$1_0))))
                                                         (let
                                                            ((_$1_0 (select HEAP$1 arrayidx$1_0))
                                                             (idxprom1$1_0 max.0$1_0))
                                                            (let
                                                               ((arrayidx2$1_0 (+ a$1_0 (* 4 idxprom1$1_0))))
                                                               (let
                                                                  ((_$1_1 (select HEAP$1 arrayidx2$1_0)))
                                                                  (let
                                                                     ((cmp3$1_0 (>= _$1_0 _$1_1)))
                                                                     (let
                                                                        ((i.0.max.0$1_0 (ite cmp3$1_0 i.0$1_0 max.0$1_0))
                                                                         (inc$1_0 (+ i.0$1_0 1)))
                                                                        (let
                                                                           ((i.0$1_0 inc$1_0)
                                                                            (max.0$1_0 i.0.max.0$1_0))
                                                                           false)))))))))))
                                          (INV_MAIN_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old HEAP$1_old a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 HEAP$2)))))))))))))))
(check-sat)
(get-model)
