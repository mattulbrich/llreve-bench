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
             (i.0$1_0 0))
            (let
               ((cmp$1_0 (<= i.0$1_0 10)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 i.0$1_0)
                      (x$2_0 x$2_0_old)
                      (i.0$2_0 10))
                     (let
                        ((cmp$2_0 (>= i.0$2_0 0)))
                        (not cmp$2_0)))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (IN_INV x$1_0_old x$2_0_old)
         (let
            ((x$1_0 x$1_0_old)
             (i.0$1_0 0))
            (let
               ((cmp$1_0 (<= i.0$1_0 10)))
               (=>
                  cmp$1_0
                  (let
                     ((x$2_0 x$2_0_old)
                      (i.0$2_0 10))
                     (let
                        ((cmp$2_0 (>= i.0$2_0 0)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((sub2$2_0 (- 10 i.0$2_0)))
                              (let
                                 ((result$2 sub2$2_0))
                                 false)))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (IN_INV x$1_0_old x$2_0_old)
         (let
            ((x$1_0 x$1_0_old)
             (i.0$1_0 0))
            (let
               ((cmp$1_0 (<= i.0$1_0 10)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 i.0$1_0)
                      (x$2_0 x$2_0_old)
                      (i.0$2_0 10))
                     (let
                        ((cmp$2_0 (>= i.0$2_0 0)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((sub2$2_0 (- 10 i.0$2_0)))
                              (let
                                 ((result$2 sub2$2_0))
                                 (OUT_INV result$1 result$2))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (IN_INV x$1_0_old x$2_0_old)
         (let
            ((x$1_0 x$1_0_old)
             (i.0$1_0 0))
            (let
               ((cmp$1_0 (<= i.0$1_0 10)))
               (=>
                  cmp$1_0
                  (let
                     ((x$2_0 x$2_0_old)
                      (i.0$2_0 10))
                     (let
                        ((cmp$2_0 (>= i.0$2_0 0)))
                        (=>
                           cmp$2_0
                           (INV_MAIN_42 i.0$1_0 x$1_0 i.0$2_0 x$2_0))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (x$1_0 x$1_0_old))
            (let
               ((cmp1$1_0 (= i.0$1_0 x$1_0)))
               (=>
                  cmp1$1_0
                  (let
                     ((result$1 i.0$1_0)
                      (i.0$2_0 i.0$2_0_old)
                      (x$2_0 x$2_0_old))
                     (let
                        ((sub$2_0 (- 10 x$2_0)))
                        (let
                           ((cmp1$2_0 (= i.0$2_0 sub$2_0)))
                           (=>
                              cmp1$2_0
                              (let
                                 ((sub2$2_0 (- 10 i.0$2_0)))
                                 (let
                                    ((result$2 sub2$2_0))
                                    (OUT_INV result$1 result$2)))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (x$1_0 x$1_0_old))
            (let
               ((cmp1$1_0 (= i.0$1_0 x$1_0)))
               (=>
                  cmp1$1_0
                  (let
                     ((result$1 i.0$1_0)
                      (i.0$2_0 i.0$2_0_old)
                      (x$2_0 x$2_0_old))
                     (let
                        ((sub$2_0 (- 10 x$2_0)))
                        (let
                           ((cmp1$2_0 (= i.0$2_0 sub$2_0)))
                           (=>
                              (not cmp1$2_0)
                              (let
                                 ((dec$2_0 (+ i.0$2_0 (- 1))))
                                 (let
                                    ((i.0$2_0 dec$2_0))
                                    (let
                                       ((cmp$2_0 (>= i.0$2_0 0)))
                                       (=>
                                          (not cmp$2_0)
                                          (let
                                             ((sub2$2_0 (- 10 i.0$2_0)))
                                             (let
                                                ((result$2 sub2$2_0))
                                                (OUT_INV result$1 result$2)))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (x$1_0 x$1_0_old))
            (let
               ((cmp1$1_0 (= i.0$1_0 x$1_0)))
               (=>
                  (not cmp1$1_0)
                  (let
                     ((inc$1_0 (+ i.0$1_0 1)))
                     (let
                        ((i.0$1_0 inc$1_0))
                        (let
                           ((cmp$1_0 (<= i.0$1_0 10)))
                           (=>
                              (not cmp$1_0)
                              (let
                                 ((result$1 i.0$1_0)
                                  (i.0$2_0 i.0$2_0_old)
                                  (x$2_0 x$2_0_old))
                                 (let
                                    ((sub$2_0 (- 10 x$2_0)))
                                    (let
                                       ((cmp1$2_0 (= i.0$2_0 sub$2_0)))
                                       (=>
                                          cmp1$2_0
                                          (let
                                             ((sub2$2_0 (- 10 i.0$2_0)))
                                             (let
                                                ((result$2 sub2$2_0))
                                                (OUT_INV result$1 result$2)))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (x$1_0 x$1_0_old))
            (let
               ((cmp1$1_0 (= i.0$1_0 x$1_0)))
               (=>
                  (not cmp1$1_0)
                  (let
                     ((inc$1_0 (+ i.0$1_0 1)))
                     (let
                        ((i.0$1_0 inc$1_0))
                        (let
                           ((cmp$1_0 (<= i.0$1_0 10)))
                           (=>
                              (not cmp$1_0)
                              (let
                                 ((result$1 i.0$1_0)
                                  (i.0$2_0 i.0$2_0_old)
                                  (x$2_0 x$2_0_old))
                                 (let
                                    ((sub$2_0 (- 10 x$2_0)))
                                    (let
                                       ((cmp1$2_0 (= i.0$2_0 sub$2_0)))
                                       (=>
                                          (not cmp1$2_0)
                                          (let
                                             ((dec$2_0 (+ i.0$2_0 (- 1))))
                                             (let
                                                ((i.0$2_0 dec$2_0))
                                                (let
                                                   ((cmp$2_0 (>= i.0$2_0 0)))
                                                   (=>
                                                      (not cmp$2_0)
                                                      (let
                                                         ((sub2$2_0 (- 10 i.0$2_0)))
                                                         (let
                                                            ((result$2 sub2$2_0))
                                                            (OUT_INV result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (x$1_0 x$1_0_old))
            (let
               ((cmp1$1_0 (= i.0$1_0 x$1_0)))
               (=>
                  (not cmp1$1_0)
                  (let
                     ((inc$1_0 (+ i.0$1_0 1)))
                     (let
                        ((i.0$1_0 inc$1_0))
                        (let
                           ((cmp$1_0 (<= i.0$1_0 10)))
                           (=>
                              cmp$1_0
                              (let
                                 ((i.0$2_0 i.0$2_0_old)
                                  (x$2_0 x$2_0_old))
                                 (let
                                    ((sub$2_0 (- 10 x$2_0)))
                                    (let
                                       ((cmp1$2_0 (= i.0$2_0 sub$2_0)))
                                       (=>
                                          (not cmp1$2_0)
                                          (let
                                             ((dec$2_0 (+ i.0$2_0 (- 1))))
                                             (let
                                                ((i.0$2_0 dec$2_0))
                                                (let
                                                   ((cmp$2_0 (>= i.0$2_0 0)))
                                                   (=>
                                                      cmp$2_0
                                                      (INV_MAIN_42 i.0$1_0 x$1_0 i.0$2_0 x$2_0)))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (x$1_0 x$1_0_old))
            (let
               ((cmp1$1_0 (= i.0$1_0 x$1_0)))
               (=>
                  (not cmp1$1_0)
                  (let
                     ((inc$1_0 (+ i.0$1_0 1)))
                     (let
                        ((i.0$1_0 inc$1_0))
                        (let
                           ((cmp$1_0 (<= i.0$1_0 10)))
                           (=>
                              cmp$1_0
                              (=>
                                 (let
                                    ((i.0$2_0 i.0$2_0_old)
                                     (x$2_0 x$2_0_old))
                                    (let
                                       ((sub$2_0 (- 10 x$2_0)))
                                       (let
                                          ((cmp1$2_0 (= i.0$2_0 sub$2_0)))
                                          (=>
                                             (not cmp1$2_0)
                                             (let
                                                ((dec$2_0 (+ i.0$2_0 (- 1))))
                                                (let
                                                   ((i.0$2_0 dec$2_0))
                                                   (let
                                                      ((cmp$2_0 (>= i.0$2_0 0)))
                                                      (not cmp$2_0))))))))
                                 (INV_MAIN_42 i.0$1_0 x$1_0 i.0$2_0_old x$2_0_old))))))))))))
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
               ((sub$2_0 (- 10 x$2_0)))
               (let
                  ((cmp1$2_0 (= i.0$2_0 sub$2_0)))
                  (=>
                     (not cmp1$2_0)
                     (let
                        ((dec$2_0 (+ i.0$2_0 (- 1))))
                        (let
                           ((i.0$2_0 dec$2_0))
                           (let
                              ((cmp$2_0 (>= i.0$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (=>
                                    (let
                                       ((i.0$1_0 i.0$1_0_old)
                                        (x$1_0 x$1_0_old))
                                       (let
                                          ((cmp1$1_0 (= i.0$1_0 x$1_0)))
                                          (=>
                                             (not cmp1$1_0)
                                             (let
                                                ((inc$1_0 (+ i.0$1_0 1)))
                                                (let
                                                   ((i.0$1_0 inc$1_0))
                                                   (let
                                                      ((cmp$1_0 (<= i.0$1_0 10)))
                                                      (not cmp$1_0)))))))
                                    (INV_MAIN_42 i.0$1_0_old x$1_0_old i.0$2_0 x$2_0)))))))))))))
(check-sat)
(get-model)
