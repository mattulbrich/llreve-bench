;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((x$1_0 Int)
    (x$2_0 Int))
   Bool
   (= x$1_0 x$2_0))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
; :annot (INV_MAIN_42 i.0$1_0 x$1_0 i.0$2_0 x$2_0)
(declare-fun
   INV_MAIN_42
   (Int
    Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (IN_INV x$1_0_old x$2_0_old)
         (let
            ((x$1_0 x$1_0_old)
             (i.0$1_0 0)
             (x$2_0 x$2_0_old)
             (i.0$2_0 0))
            (INV_MAIN_42 i.0$1_0 x$1_0 i.0$2_0 x$2_0)))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old))
            (let
               ((x$1_0 x$1_0_old)
                (cmp$1_0 (<= i.0$1_0 10)))
               (let
                  ((conv$1_0 (ite cmp$1_0 1 0)))
                  (let
                     ((tobool$1_0 (= conv$1_0 0))
                      (cmp1$1_0 (= i.0$1_0 x$1_0)))
                     (let
                        ((or.cond$1_0 (or
                                          tobool$1_0
                                          cmp1$1_0)))
                        (=>
                           or.cond$1_0
                           (let
                              ((result$1 i.0$1_0)
                               (i.0$2_0 i.0$2_0_old)
                               (x$2_0 x$2_0_old))
                              (let
                                 ((cmp$2_0 (<= i.0$2_0 10))
                                  (cmp1$2_0 (distinct i.0$2_0 x$2_0)))
                                 (let
                                    ((cmp1.$2_0 (ite cmp$2_0 cmp1$2_0 false)))
                                    (=>
                                       (not cmp1.$2_0)
                                       (let
                                          ((result$2 i.0$2_0))
                                          (OUT_INV result$1 result$2)))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old))
            (let
               ((x$1_0 x$1_0_old)
                (cmp$1_0 (<= i.0$1_0 10)))
               (let
                  ((conv$1_0 (ite cmp$1_0 1 0)))
                  (let
                     ((tobool$1_0 (= conv$1_0 0))
                      (cmp1$1_0 (= i.0$1_0 x$1_0)))
                     (let
                        ((or.cond$1_0 (or
                                          tobool$1_0
                                          cmp1$1_0)))
                        (=>
                           (not or.cond$1_0)
                           (let
                              ((inc$1_0 (+ i.0$1_0 1)))
                              (let
                                 ((i.0$1_0 inc$1_0)
                                  (i.0$2_0 i.0$2_0_old)
                                  (x$2_0 x$2_0_old))
                                 (let
                                    ((cmp$2_0 (<= i.0$2_0 10))
                                     (cmp1$2_0 (distinct i.0$2_0 x$2_0)))
                                    (let
                                       ((cmp1.$2_0 (ite cmp$2_0 cmp1$2_0 false)))
                                       (=>
                                          cmp1.$2_0
                                          (let
                                             ((inc$2_0 (+ i.0$2_0 1)))
                                             (let
                                                ((i.0$2_0 inc$2_0))
                                                (INV_MAIN_42 i.0$1_0 x$1_0 i.0$2_0 x$2_0)))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old))
            (let
               ((x$1_0 x$1_0_old)
                (cmp$1_0 (<= i.0$1_0 10)))
               (let
                  ((conv$1_0 (ite cmp$1_0 1 0)))
                  (let
                     ((tobool$1_0 (= conv$1_0 0))
                      (cmp1$1_0 (= i.0$1_0 x$1_0)))
                     (let
                        ((or.cond$1_0 (or
                                          tobool$1_0
                                          cmp1$1_0)))
                        (=>
                           (not or.cond$1_0)
                           (let
                              ((inc$1_0 (+ i.0$1_0 1)))
                              (let
                                 ((i.0$1_0 inc$1_0))
                                 (=>
                                    (let
                                       ((i.0$2_0 i.0$2_0_old)
                                        (x$2_0 x$2_0_old))
                                       (let
                                          ((cmp$2_0 (<= i.0$2_0 10))
                                           (cmp1$2_0 (distinct i.0$2_0 x$2_0)))
                                          (let
                                             ((cmp1.$2_0 (ite cmp$2_0 cmp1$2_0 false)))
                                             (=>
                                                cmp1.$2_0
                                                (let
                                                   ((inc$2_0 (+ i.0$2_0 1)))
                                                   (let
                                                      ((i.0$2_0 inc$2_0))
                                                      false))))))
                                    (INV_MAIN_42 i.0$1_0 x$1_0 i.0$2_0_old x$2_0_old)))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((i.0$2_0 i.0$2_0_old)
             (x$2_0 x$2_0_old))
            (let
               ((cmp$2_0 (<= i.0$2_0 10))
                (cmp1$2_0 (distinct i.0$2_0 x$2_0)))
               (let
                  ((cmp1.$2_0 (ite cmp$2_0 cmp1$2_0 false)))
                  (=>
                     cmp1.$2_0
                     (let
                        ((inc$2_0 (+ i.0$2_0 1)))
                        (let
                           ((i.0$2_0 inc$2_0))
                           (=>
                              (let
                                 ((i.0$1_0 i.0$1_0_old))
                                 (let
                                    ((x$1_0 x$1_0_old)
                                     (cmp$1_0 (<= i.0$1_0 10)))
                                    (let
                                       ((conv$1_0 (ite cmp$1_0 1 0)))
                                       (let
                                          ((tobool$1_0 (= conv$1_0 0))
                                           (cmp1$1_0 (= i.0$1_0 x$1_0)))
                                          (let
                                             ((or.cond$1_0 (or
                                                               tobool$1_0
                                                               cmp1$1_0)))
                                             (=>
                                                (not or.cond$1_0)
                                                (let
                                                   ((inc$1_0 (+ i.0$1_0 1)))
                                                   (let
                                                      ((i.0$1_0 inc$1_0))
                                                      false))))))))
                              (INV_MAIN_42 i.0$1_0_old x$1_0_old i.0$2_0 x$2_0)))))))))))
(check-sat)
(get-model)
