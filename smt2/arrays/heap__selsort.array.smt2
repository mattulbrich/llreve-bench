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
; :annot (INV_MAIN_1 a$1_0 i.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 n$2_0 HEAP$2)
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
; :annot (INV_MAIN_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 j.0$2_0 n$2_0 HEAP$2)
(declare-fun
   INV_MAIN_2
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
             (i.0$1_0 0)
             (a$2_0 a$2_0_old)
             (n$2_0 n$2_0_old)
             (HEAP$2 HEAP$2_old)
             (i.0$2_0 0))
            (INV_MAIN_1 a$1_0 i.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 n$2_0 HEAP$2)))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 a$1_0_old i.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 n$1_0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 0)
                      (HEAP$1_res HEAP$1)
                      (a$2_0 a$2_0_old)
                      (i.0$2_0 i.0$2_0_old)
                      (n$2_0 n$2_0_old))
                     (let
                        ((HEAP$2 HEAP$2_old)
                         (cmp$2_0 (< i.0$2_0 n$2_0)))
                        (=>
                           cmp$2_0
                           (let
                              ((j.0$2_0 i.0$2_0))
                              false))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 a$1_0_old i.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 n$1_0)))
               (=>
                  cmp$1_0
                  (let
                     ((j.0$1_0 i.0$1_0)
                      (a$2_0 a$2_0_old)
                      (i.0$2_0 i.0$2_0_old)
                      (n$2_0 n$2_0_old))
                     (let
                        ((HEAP$2 HEAP$2_old)
                         (cmp$2_0 (< i.0$2_0 n$2_0)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((result$2 0)
                               (HEAP$2_res HEAP$2))
                              false))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 a$1_0_old i.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 n$1_0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 0)
                      (HEAP$1_res HEAP$1)
                      (a$2_0 a$2_0_old)
                      (i.0$2_0 i.0$2_0_old)
                      (n$2_0 n$2_0_old))
                     (let
                        ((HEAP$2 HEAP$2_old)
                         (cmp$2_0 (< i.0$2_0 n$2_0)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((result$2 0)
                               (HEAP$2_res HEAP$2))
                              (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 a$1_0_old i.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 n$1_0)))
               (=>
                  cmp$1_0
                  (let
                     ((j.0$1_0 i.0$1_0)
                      (a$2_0 a$2_0_old)
                      (i.0$2_0 i.0$2_0_old)
                      (n$2_0 n$2_0_old))
                     (let
                        ((HEAP$2 HEAP$2_old)
                         (cmp$2_0 (< i.0$2_0 n$2_0)))
                        (=>
                           cmp$2_0
                           (let
                              ((j.0$2_0 i.0$2_0))
                              (INV_MAIN_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 j.0$2_0 n$2_0 HEAP$2)))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp3$1_0 (< j.0$1_0 n$1_0)))
               (=>
                  (not cmp3$1_0)
                  (let
                     ((inc20$1_0 (+ i.0$1_0 1)))
                     (let
                        ((i.0$1_0 inc20$1_0)
                         (a$2_0 a$2_0_old)
                         (i.0$2_0 i.0$2_0_old)
                         (j.0$2_0 j.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (cmp3$2_0 (< j.0$2_0 n$2_0)))
                           (=>
                              cmp3$2_0
                              (let
                                 ((idxprom$2_0 j.0$2_0))
                                 (let
                                    ((arrayidx$2_0 (+ a$2_0 (* 4 idxprom$2_0))))
                                    (let
                                       ((_$2_0 (select HEAP$2 arrayidx$2_0))
                                        (idxprom8$2_0 i.0$2_0))
                                       (let
                                          ((arrayidx9$2_0 (+ a$2_0 (* 4 idxprom8$2_0))))
                                          (let
                                             ((_$2_1 (select HEAP$2 arrayidx9$2_0)))
                                             (let
                                                ((cmp10$2_0 (< _$2_0 _$2_1)))
                                                (=>
                                                   cmp10$2_0
                                                   (let
                                                      ((idxprom12$2_0 i.0$2_0))
                                                      (let
                                                         ((arrayidx13$2_0 (+ a$2_0 (* 4 idxprom12$2_0))))
                                                         (let
                                                            ((_$2_2 (select HEAP$2 arrayidx13$2_0))
                                                             (idxprom14$2_0 j.0$2_0))
                                                            (let
                                                               ((arrayidx15$2_0 (+ a$2_0 (* 4 idxprom14$2_0))))
                                                               (let
                                                                  ((_$2_3 (select HEAP$2 arrayidx15$2_0))
                                                                   (idxprom16$2_0 i.0$2_0))
                                                                  (let
                                                                     ((arrayidx17$2_0 (+ a$2_0 (* 4 idxprom16$2_0))))
                                                                     (let
                                                                        ((HEAP$2 (store HEAP$2 arrayidx17$2_0 _$2_3))
                                                                         (idxprom18$2_0 j.0$2_0))
                                                                        (let
                                                                           ((arrayidx19$2_0 (+ a$2_0 (* 4 idxprom18$2_0))))
                                                                           (let
                                                                              ((HEAP$2 (store HEAP$2 arrayidx19$2_0 _$2_2))
                                                                               (inc$2_0 (+ j.0$2_0 1)))
                                                                              (let
                                                                                 ((j.0$2_0 inc$2_0))
                                                                                 false)))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp3$1_0 (< j.0$1_0 n$1_0)))
               (=>
                  (not cmp3$1_0)
                  (let
                     ((inc20$1_0 (+ i.0$1_0 1)))
                     (let
                        ((i.0$1_0 inc20$1_0)
                         (a$2_0 a$2_0_old)
                         (i.0$2_0 i.0$2_0_old)
                         (j.0$2_0 j.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (cmp3$2_0 (< j.0$2_0 n$2_0)))
                           (=>
                              cmp3$2_0
                              (let
                                 ((idxprom$2_0 j.0$2_0))
                                 (let
                                    ((arrayidx$2_0 (+ a$2_0 (* 4 idxprom$2_0))))
                                    (let
                                       ((_$2_0 (select HEAP$2 arrayidx$2_0))
                                        (idxprom8$2_0 i.0$2_0))
                                       (let
                                          ((arrayidx9$2_0 (+ a$2_0 (* 4 idxprom8$2_0))))
                                          (let
                                             ((_$2_1 (select HEAP$2 arrayidx9$2_0)))
                                             (let
                                                ((cmp10$2_0 (< _$2_0 _$2_1)))
                                                (=>
                                                   (not cmp10$2_0)
                                                   (let
                                                      ((inc$2_0 (+ j.0$2_0 1)))
                                                      (let
                                                         ((j.0$2_0 inc$2_0))
                                                         false)))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp3$1_0 (< j.0$1_0 n$1_0)))
               (=>
                  cmp3$1_0
                  (let
                     ((idxprom$1_0 j.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ a$1_0 (* 4 idxprom$1_0))))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0))
                            (idxprom8$1_0 i.0$1_0))
                           (let
                              ((arrayidx9$1_0 (+ a$1_0 (* 4 idxprom8$1_0))))
                              (let
                                 ((_$1_1 (select HEAP$1 arrayidx9$1_0)))
                                 (let
                                    ((cmp10$1_0 (<= _$1_0 _$1_1)))
                                    (=>
                                       cmp10$1_0
                                       (let
                                          ((idxprom12$1_0 i.0$1_0))
                                          (let
                                             ((arrayidx13$1_0 (+ a$1_0 (* 4 idxprom12$1_0))))
                                             (let
                                                ((_$1_2 (select HEAP$1 arrayidx13$1_0))
                                                 (idxprom14$1_0 j.0$1_0))
                                                (let
                                                   ((arrayidx15$1_0 (+ a$1_0 (* 4 idxprom14$1_0))))
                                                   (let
                                                      ((_$1_3 (select HEAP$1 arrayidx15$1_0))
                                                       (idxprom16$1_0 i.0$1_0))
                                                      (let
                                                         ((arrayidx17$1_0 (+ a$1_0 (* 4 idxprom16$1_0))))
                                                         (let
                                                            ((HEAP$1 (store HEAP$1 arrayidx17$1_0 _$1_3))
                                                             (idxprom18$1_0 j.0$1_0))
                                                            (let
                                                               ((arrayidx19$1_0 (+ a$1_0 (* 4 idxprom18$1_0))))
                                                               (let
                                                                  ((HEAP$1 (store HEAP$1 arrayidx19$1_0 _$1_2))
                                                                   (inc$1_0 (+ j.0$1_0 1)))
                                                                  (let
                                                                     ((j.0$1_0 inc$1_0)
                                                                      (a$2_0 a$2_0_old)
                                                                      (i.0$2_0 i.0$2_0_old)
                                                                      (j.0$2_0 j.0$2_0_old)
                                                                      (n$2_0 n$2_0_old))
                                                                     (let
                                                                        ((HEAP$2 HEAP$2_old)
                                                                         (cmp3$2_0 (< j.0$2_0 n$2_0)))
                                                                        (=>
                                                                           (not cmp3$2_0)
                                                                           (let
                                                                              ((inc20$2_0 (+ i.0$2_0 1)))
                                                                              (let
                                                                                 ((i.0$2_0 inc20$2_0))
                                                                                 false)))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp3$1_0 (< j.0$1_0 n$1_0)))
               (=>
                  cmp3$1_0
                  (let
                     ((idxprom$1_0 j.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ a$1_0 (* 4 idxprom$1_0))))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0))
                            (idxprom8$1_0 i.0$1_0))
                           (let
                              ((arrayidx9$1_0 (+ a$1_0 (* 4 idxprom8$1_0))))
                              (let
                                 ((_$1_1 (select HEAP$1 arrayidx9$1_0)))
                                 (let
                                    ((cmp10$1_0 (<= _$1_0 _$1_1)))
                                    (=>
                                       (not cmp10$1_0)
                                       (let
                                          ((inc$1_0 (+ j.0$1_0 1)))
                                          (let
                                             ((j.0$1_0 inc$1_0)
                                              (a$2_0 a$2_0_old)
                                              (i.0$2_0 i.0$2_0_old)
                                              (j.0$2_0 j.0$2_0_old)
                                              (n$2_0 n$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (cmp3$2_0 (< j.0$2_0 n$2_0)))
                                                (=>
                                                   (not cmp3$2_0)
                                                   (let
                                                      ((inc20$2_0 (+ i.0$2_0 1)))
                                                      (let
                                                         ((i.0$2_0 inc20$2_0))
                                                         false)))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp3$1_0 (< j.0$1_0 n$1_0)))
               (=>
                  (not cmp3$1_0)
                  (let
                     ((inc20$1_0 (+ i.0$1_0 1)))
                     (let
                        ((i.0$1_0 inc20$1_0)
                         (a$2_0 a$2_0_old)
                         (i.0$2_0 i.0$2_0_old)
                         (j.0$2_0 j.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (cmp3$2_0 (< j.0$2_0 n$2_0)))
                           (=>
                              (not cmp3$2_0)
                              (let
                                 ((inc20$2_0 (+ i.0$2_0 1)))
                                 (let
                                    ((i.0$2_0 inc20$2_0))
                                    (INV_MAIN_1 a$1_0 i.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 n$2_0 HEAP$2)))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp3$1_0 (< j.0$1_0 n$1_0)))
               (=>
                  cmp3$1_0
                  (let
                     ((idxprom$1_0 j.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ a$1_0 (* 4 idxprom$1_0))))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0))
                            (idxprom8$1_0 i.0$1_0))
                           (let
                              ((arrayidx9$1_0 (+ a$1_0 (* 4 idxprom8$1_0))))
                              (let
                                 ((_$1_1 (select HEAP$1 arrayidx9$1_0)))
                                 (let
                                    ((cmp10$1_0 (<= _$1_0 _$1_1)))
                                    (=>
                                       cmp10$1_0
                                       (let
                                          ((idxprom12$1_0 i.0$1_0))
                                          (let
                                             ((arrayidx13$1_0 (+ a$1_0 (* 4 idxprom12$1_0))))
                                             (let
                                                ((_$1_2 (select HEAP$1 arrayidx13$1_0))
                                                 (idxprom14$1_0 j.0$1_0))
                                                (let
                                                   ((arrayidx15$1_0 (+ a$1_0 (* 4 idxprom14$1_0))))
                                                   (let
                                                      ((_$1_3 (select HEAP$1 arrayidx15$1_0))
                                                       (idxprom16$1_0 i.0$1_0))
                                                      (let
                                                         ((arrayidx17$1_0 (+ a$1_0 (* 4 idxprom16$1_0))))
                                                         (let
                                                            ((HEAP$1 (store HEAP$1 arrayidx17$1_0 _$1_3))
                                                             (idxprom18$1_0 j.0$1_0))
                                                            (let
                                                               ((arrayidx19$1_0 (+ a$1_0 (* 4 idxprom18$1_0))))
                                                               (let
                                                                  ((HEAP$1 (store HEAP$1 arrayidx19$1_0 _$1_2))
                                                                   (inc$1_0 (+ j.0$1_0 1)))
                                                                  (let
                                                                     ((j.0$1_0 inc$1_0)
                                                                      (a$2_0 a$2_0_old)
                                                                      (i.0$2_0 i.0$2_0_old)
                                                                      (j.0$2_0 j.0$2_0_old)
                                                                      (n$2_0 n$2_0_old))
                                                                     (let
                                                                        ((HEAP$2 HEAP$2_old)
                                                                         (cmp3$2_0 (< j.0$2_0 n$2_0)))
                                                                        (=>
                                                                           cmp3$2_0
                                                                           (let
                                                                              ((idxprom$2_0 j.0$2_0))
                                                                              (let
                                                                                 ((arrayidx$2_0 (+ a$2_0 (* 4 idxprom$2_0))))
                                                                                 (let
                                                                                    ((_$2_0 (select HEAP$2 arrayidx$2_0))
                                                                                     (idxprom8$2_0 i.0$2_0))
                                                                                    (let
                                                                                       ((arrayidx9$2_0 (+ a$2_0 (* 4 idxprom8$2_0))))
                                                                                       (let
                                                                                          ((_$2_1 (select HEAP$2 arrayidx9$2_0)))
                                                                                          (let
                                                                                             ((cmp10$2_0 (< _$2_0 _$2_1)))
                                                                                             (=>
                                                                                                cmp10$2_0
                                                                                                (let
                                                                                                   ((idxprom12$2_0 i.0$2_0))
                                                                                                   (let
                                                                                                      ((arrayidx13$2_0 (+ a$2_0 (* 4 idxprom12$2_0))))
                                                                                                      (let
                                                                                                         ((_$2_2 (select HEAP$2 arrayidx13$2_0))
                                                                                                          (idxprom14$2_0 j.0$2_0))
                                                                                                         (let
                                                                                                            ((arrayidx15$2_0 (+ a$2_0 (* 4 idxprom14$2_0))))
                                                                                                            (let
                                                                                                               ((_$2_3 (select HEAP$2 arrayidx15$2_0))
                                                                                                                (idxprom16$2_0 i.0$2_0))
                                                                                                               (let
                                                                                                                  ((arrayidx17$2_0 (+ a$2_0 (* 4 idxprom16$2_0))))
                                                                                                                  (let
                                                                                                                     ((HEAP$2 (store HEAP$2 arrayidx17$2_0 _$2_3))
                                                                                                                      (idxprom18$2_0 j.0$2_0))
                                                                                                                     (let
                                                                                                                        ((arrayidx19$2_0 (+ a$2_0 (* 4 idxprom18$2_0))))
                                                                                                                        (let
                                                                                                                           ((HEAP$2 (store HEAP$2 arrayidx19$2_0 _$2_2))
                                                                                                                            (inc$2_0 (+ j.0$2_0 1)))
                                                                                                                           (let
                                                                                                                              ((j.0$2_0 inc$2_0))
                                                                                                                              (INV_MAIN_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 j.0$2_0 n$2_0 HEAP$2)))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp3$1_0 (< j.0$1_0 n$1_0)))
               (=>
                  cmp3$1_0
                  (let
                     ((idxprom$1_0 j.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ a$1_0 (* 4 idxprom$1_0))))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0))
                            (idxprom8$1_0 i.0$1_0))
                           (let
                              ((arrayidx9$1_0 (+ a$1_0 (* 4 idxprom8$1_0))))
                              (let
                                 ((_$1_1 (select HEAP$1 arrayidx9$1_0)))
                                 (let
                                    ((cmp10$1_0 (<= _$1_0 _$1_1)))
                                    (=>
                                       cmp10$1_0
                                       (let
                                          ((idxprom12$1_0 i.0$1_0))
                                          (let
                                             ((arrayidx13$1_0 (+ a$1_0 (* 4 idxprom12$1_0))))
                                             (let
                                                ((_$1_2 (select HEAP$1 arrayidx13$1_0))
                                                 (idxprom14$1_0 j.0$1_0))
                                                (let
                                                   ((arrayidx15$1_0 (+ a$1_0 (* 4 idxprom14$1_0))))
                                                   (let
                                                      ((_$1_3 (select HEAP$1 arrayidx15$1_0))
                                                       (idxprom16$1_0 i.0$1_0))
                                                      (let
                                                         ((arrayidx17$1_0 (+ a$1_0 (* 4 idxprom16$1_0))))
                                                         (let
                                                            ((HEAP$1 (store HEAP$1 arrayidx17$1_0 _$1_3))
                                                             (idxprom18$1_0 j.0$1_0))
                                                            (let
                                                               ((arrayidx19$1_0 (+ a$1_0 (* 4 idxprom18$1_0))))
                                                               (let
                                                                  ((HEAP$1 (store HEAP$1 arrayidx19$1_0 _$1_2))
                                                                   (inc$1_0 (+ j.0$1_0 1)))
                                                                  (let
                                                                     ((j.0$1_0 inc$1_0)
                                                                      (a$2_0 a$2_0_old)
                                                                      (i.0$2_0 i.0$2_0_old)
                                                                      (j.0$2_0 j.0$2_0_old)
                                                                      (n$2_0 n$2_0_old))
                                                                     (let
                                                                        ((HEAP$2 HEAP$2_old)
                                                                         (cmp3$2_0 (< j.0$2_0 n$2_0)))
                                                                        (=>
                                                                           cmp3$2_0
                                                                           (let
                                                                              ((idxprom$2_0 j.0$2_0))
                                                                              (let
                                                                                 ((arrayidx$2_0 (+ a$2_0 (* 4 idxprom$2_0))))
                                                                                 (let
                                                                                    ((_$2_0 (select HEAP$2 arrayidx$2_0))
                                                                                     (idxprom8$2_0 i.0$2_0))
                                                                                    (let
                                                                                       ((arrayidx9$2_0 (+ a$2_0 (* 4 idxprom8$2_0))))
                                                                                       (let
                                                                                          ((_$2_1 (select HEAP$2 arrayidx9$2_0)))
                                                                                          (let
                                                                                             ((cmp10$2_0 (< _$2_0 _$2_1)))
                                                                                             (=>
                                                                                                (not cmp10$2_0)
                                                                                                (let
                                                                                                   ((inc$2_0 (+ j.0$2_0 1)))
                                                                                                   (let
                                                                                                      ((j.0$2_0 inc$2_0))
                                                                                                      (INV_MAIN_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 j.0$2_0 n$2_0 HEAP$2)))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp3$1_0 (< j.0$1_0 n$1_0)))
               (=>
                  cmp3$1_0
                  (let
                     ((idxprom$1_0 j.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ a$1_0 (* 4 idxprom$1_0))))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0))
                            (idxprom8$1_0 i.0$1_0))
                           (let
                              ((arrayidx9$1_0 (+ a$1_0 (* 4 idxprom8$1_0))))
                              (let
                                 ((_$1_1 (select HEAP$1 arrayidx9$1_0)))
                                 (let
                                    ((cmp10$1_0 (<= _$1_0 _$1_1)))
                                    (=>
                                       (not cmp10$1_0)
                                       (let
                                          ((inc$1_0 (+ j.0$1_0 1)))
                                          (let
                                             ((j.0$1_0 inc$1_0)
                                              (a$2_0 a$2_0_old)
                                              (i.0$2_0 i.0$2_0_old)
                                              (j.0$2_0 j.0$2_0_old)
                                              (n$2_0 n$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (cmp3$2_0 (< j.0$2_0 n$2_0)))
                                                (=>
                                                   cmp3$2_0
                                                   (let
                                                      ((idxprom$2_0 j.0$2_0))
                                                      (let
                                                         ((arrayidx$2_0 (+ a$2_0 (* 4 idxprom$2_0))))
                                                         (let
                                                            ((_$2_0 (select HEAP$2 arrayidx$2_0))
                                                             (idxprom8$2_0 i.0$2_0))
                                                            (let
                                                               ((arrayidx9$2_0 (+ a$2_0 (* 4 idxprom8$2_0))))
                                                               (let
                                                                  ((_$2_1 (select HEAP$2 arrayidx9$2_0)))
                                                                  (let
                                                                     ((cmp10$2_0 (< _$2_0 _$2_1)))
                                                                     (=>
                                                                        cmp10$2_0
                                                                        (let
                                                                           ((idxprom12$2_0 i.0$2_0))
                                                                           (let
                                                                              ((arrayidx13$2_0 (+ a$2_0 (* 4 idxprom12$2_0))))
                                                                              (let
                                                                                 ((_$2_2 (select HEAP$2 arrayidx13$2_0))
                                                                                  (idxprom14$2_0 j.0$2_0))
                                                                                 (let
                                                                                    ((arrayidx15$2_0 (+ a$2_0 (* 4 idxprom14$2_0))))
                                                                                    (let
                                                                                       ((_$2_3 (select HEAP$2 arrayidx15$2_0))
                                                                                        (idxprom16$2_0 i.0$2_0))
                                                                                       (let
                                                                                          ((arrayidx17$2_0 (+ a$2_0 (* 4 idxprom16$2_0))))
                                                                                          (let
                                                                                             ((HEAP$2 (store HEAP$2 arrayidx17$2_0 _$2_3))
                                                                                              (idxprom18$2_0 j.0$2_0))
                                                                                             (let
                                                                                                ((arrayidx19$2_0 (+ a$2_0 (* 4 idxprom18$2_0))))
                                                                                                (let
                                                                                                   ((HEAP$2 (store HEAP$2 arrayidx19$2_0 _$2_2))
                                                                                                    (inc$2_0 (+ j.0$2_0 1)))
                                                                                                   (let
                                                                                                      ((j.0$2_0 inc$2_0))
                                                                                                      (INV_MAIN_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 j.0$2_0 n$2_0 HEAP$2)))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old HEAP$1_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp3$1_0 (< j.0$1_0 n$1_0)))
               (=>
                  cmp3$1_0
                  (let
                     ((idxprom$1_0 j.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ a$1_0 (* 4 idxprom$1_0))))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0))
                            (idxprom8$1_0 i.0$1_0))
                           (let
                              ((arrayidx9$1_0 (+ a$1_0 (* 4 idxprom8$1_0))))
                              (let
                                 ((_$1_1 (select HEAP$1 arrayidx9$1_0)))
                                 (let
                                    ((cmp10$1_0 (<= _$1_0 _$1_1)))
                                    (=>
                                       (not cmp10$1_0)
                                       (let
                                          ((inc$1_0 (+ j.0$1_0 1)))
                                          (let
                                             ((j.0$1_0 inc$1_0)
                                              (a$2_0 a$2_0_old)
                                              (i.0$2_0 i.0$2_0_old)
                                              (j.0$2_0 j.0$2_0_old)
                                              (n$2_0 n$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (cmp3$2_0 (< j.0$2_0 n$2_0)))
                                                (=>
                                                   cmp3$2_0
                                                   (let
                                                      ((idxprom$2_0 j.0$2_0))
                                                      (let
                                                         ((arrayidx$2_0 (+ a$2_0 (* 4 idxprom$2_0))))
                                                         (let
                                                            ((_$2_0 (select HEAP$2 arrayidx$2_0))
                                                             (idxprom8$2_0 i.0$2_0))
                                                            (let
                                                               ((arrayidx9$2_0 (+ a$2_0 (* 4 idxprom8$2_0))))
                                                               (let
                                                                  ((_$2_1 (select HEAP$2 arrayidx9$2_0)))
                                                                  (let
                                                                     ((cmp10$2_0 (< _$2_0 _$2_1)))
                                                                     (=>
                                                                        (not cmp10$2_0)
                                                                        (let
                                                                           ((inc$2_0 (+ j.0$2_0 1)))
                                                                           (let
                                                                              ((j.0$2_0 inc$2_0))
                                                                              (INV_MAIN_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 HEAP$1 a$2_0 i.0$2_0 j.0$2_0 n$2_0 HEAP$2)))))))))))))))))))))))))))
(check-sat)
(get-model)
