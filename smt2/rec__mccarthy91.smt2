;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((a$1_0 Int)
    (x$2_0 Int))
   Bool
   (= a$1_0 x$2_0))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
(declare-fun
   INV_REC_f^f
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f^f_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1_PRE
   (Int)
   Bool)
(declare-fun
   INV_REC_f__2
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__2_PRE
   (Int)
   Bool)
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (IN_INV a$1_0_old x$2_0_old)
         (let
            ((a$1_0 a$1_0_old))
            (let
               ((cmp$1_0 (> a$1_0 100)))
               (=>
                  cmp$1_0
                  (let
                     ((sub$1_0 (- a$1_0 10)))
                     (let
                        ((r.0$1_0 sub$1_0))
                        (let
                           ((result$1 r.0$1_0)
                            (x$2_0 x$2_0_old))
                           (let
                              ((cmp$2_0 (< x$2_0 101)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((add$2_0 (+ 11 x$2_0)))
                                    (and
                                       (INV_REC_f__2_PRE add$2_0)
                                       (forall
                                          ((call$2_0 Int))
                                          (=>
                                             (INV_REC_f__2 add$2_0 call$2_0)
                                             (and
                                                (INV_REC_f__2_PRE call$2_0)
                                                (forall
                                                   ((call1$2_0 Int))
                                                   (=>
                                                      (INV_REC_f__2 call$2_0 call1$2_0)
                                                      (let
                                                         ((r.0$2_0 call1$2_0))
                                                         (let
                                                            ((result$2 r.0$2_0))
                                                            (OUT_INV result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (IN_INV a$1_0_old x$2_0_old)
         (let
            ((a$1_0 a$1_0_old))
            (let
               ((cmp$1_0 (> a$1_0 100)))
               (=>
                  cmp$1_0
                  (let
                     ((sub$1_0 (- a$1_0 10)))
                     (let
                        ((r.0$1_0 sub$1_0))
                        (let
                           ((result$1 r.0$1_0)
                            (x$2_0 x$2_0_old))
                           (let
                              ((cmp$2_0 (< x$2_0 101)))
                              (=>
                                 (not cmp$2_0)
                                 (let
                                    ((sub$2_0 (- x$2_0 10)))
                                    (let
                                       ((r.0$2_0 sub$2_0))
                                       (let
                                          ((result$2 r.0$2_0))
                                          (OUT_INV result$1 result$2)))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (IN_INV a$1_0_old x$2_0_old)
         (let
            ((a$1_0 a$1_0_old))
            (let
               ((cmp$1_0 (> a$1_0 100)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((add$1_0 (+ a$1_0 11))
                      (x$2_0 x$2_0_old))
                     (let
                        ((cmp$2_0 (< x$2_0 101)))
                        (=>
                           cmp$2_0
                           (let
                              ((add$2_0 (+ 11 x$2_0)))
                              (and
                                 (INV_REC_f^f_PRE add$1_0 add$2_0)
                                 (forall
                                    ((call$1_0 Int)
                                     (call$2_0 Int))
                                    (=>
                                       (INV_REC_f^f add$1_0 add$2_0 call$1_0 call$2_0)
                                       (and
                                          (INV_REC_f^f_PRE call$1_0 call$2_0)
                                          (forall
                                             ((call1$1_0 Int)
                                              (call1$2_0 Int))
                                             (=>
                                                (INV_REC_f^f call$1_0 call$2_0 call1$1_0 call1$2_0)
                                                (let
                                                   ((r.0$1_0 call1$1_0))
                                                   (let
                                                      ((result$1 r.0$1_0)
                                                       (r.0$2_0 call1$2_0))
                                                      (let
                                                         ((result$2 r.0$2_0))
                                                         (OUT_INV result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (IN_INV a$1_0_old x$2_0_old)
         (let
            ((a$1_0 a$1_0_old))
            (let
               ((cmp$1_0 (> a$1_0 100)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((add$1_0 (+ a$1_0 11))
                      (x$2_0 x$2_0_old))
                     (let
                        ((cmp$2_0 (< x$2_0 101)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((sub$2_0 (- x$2_0 10)))
                              (let
                                 ((r.0$2_0 sub$2_0))
                                 (let
                                    ((result$2 r.0$2_0))
                                    (and
                                       (INV_REC_f__1_PRE add$1_0)
                                       (forall
                                          ((call$1_0 Int))
                                          (=>
                                             (INV_REC_f__1 add$1_0 call$1_0)
                                             (and
                                                (INV_REC_f__1_PRE call$1_0)
                                                (forall
                                                   ((call1$1_0 Int))
                                                   (=>
                                                      (INV_REC_f__1 call$1_0 call1$1_0)
                                                      (let
                                                         ((r.0$1_0 call1$1_0))
                                                         (let
                                                            ((result$1 r.0$1_0))
                                                            (OUT_INV result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE a$1_0_old x$2_0_old)
         (let
            ((a$1_0 a$1_0_old))
            (let
               ((cmp$1_0 (> a$1_0 100)))
               (=>
                  cmp$1_0
                  (let
                     ((sub$1_0 (- a$1_0 10)))
                     (let
                        ((r.0$1_0 sub$1_0))
                        (let
                           ((result$1 r.0$1_0)
                            (x$2_0 x$2_0_old))
                           (let
                              ((cmp$2_0 (< x$2_0 101)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((add$2_0 (+ 11 x$2_0)))
                                    (and
                                       (INV_REC_f__2_PRE add$2_0)
                                       (forall
                                          ((call$2_0 Int))
                                          (=>
                                             (INV_REC_f__2 add$2_0 call$2_0)
                                             (and
                                                (INV_REC_f__2_PRE call$2_0)
                                                (forall
                                                   ((call1$2_0 Int))
                                                   (=>
                                                      (INV_REC_f__2 call$2_0 call1$2_0)
                                                      (let
                                                         ((r.0$2_0 call1$2_0))
                                                         (let
                                                            ((result$2 r.0$2_0))
                                                            (INV_REC_f^f a$1_0_old x$2_0_old result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE a$1_0_old x$2_0_old)
         (let
            ((a$1_0 a$1_0_old))
            (let
               ((cmp$1_0 (> a$1_0 100)))
               (=>
                  cmp$1_0
                  (let
                     ((sub$1_0 (- a$1_0 10)))
                     (let
                        ((r.0$1_0 sub$1_0))
                        (let
                           ((result$1 r.0$1_0)
                            (x$2_0 x$2_0_old))
                           (let
                              ((cmp$2_0 (< x$2_0 101)))
                              (=>
                                 (not cmp$2_0)
                                 (let
                                    ((sub$2_0 (- x$2_0 10)))
                                    (let
                                       ((r.0$2_0 sub$2_0))
                                       (let
                                          ((result$2 r.0$2_0))
                                          (INV_REC_f^f a$1_0_old x$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE a$1_0_old x$2_0_old)
         (let
            ((a$1_0 a$1_0_old))
            (let
               ((cmp$1_0 (> a$1_0 100)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((add$1_0 (+ a$1_0 11))
                      (x$2_0 x$2_0_old))
                     (let
                        ((cmp$2_0 (< x$2_0 101)))
                        (=>
                           cmp$2_0
                           (let
                              ((add$2_0 (+ 11 x$2_0)))
                              (and
                                 (INV_REC_f^f_PRE add$1_0 add$2_0)
                                 (forall
                                    ((call$1_0 Int)
                                     (call$2_0 Int))
                                    (=>
                                       (INV_REC_f^f add$1_0 add$2_0 call$1_0 call$2_0)
                                       (and
                                          (INV_REC_f^f_PRE call$1_0 call$2_0)
                                          (forall
                                             ((call1$1_0 Int)
                                              (call1$2_0 Int))
                                             (=>
                                                (INV_REC_f^f call$1_0 call$2_0 call1$1_0 call1$2_0)
                                                (let
                                                   ((r.0$1_0 call1$1_0))
                                                   (let
                                                      ((result$1 r.0$1_0)
                                                       (r.0$2_0 call1$2_0))
                                                      (let
                                                         ((result$2 r.0$2_0))
                                                         (INV_REC_f^f a$1_0_old x$2_0_old result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE a$1_0_old x$2_0_old)
         (let
            ((a$1_0 a$1_0_old))
            (let
               ((cmp$1_0 (> a$1_0 100)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((add$1_0 (+ a$1_0 11))
                      (x$2_0 x$2_0_old))
                     (let
                        ((cmp$2_0 (< x$2_0 101)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((sub$2_0 (- x$2_0 10)))
                              (let
                                 ((r.0$2_0 sub$2_0))
                                 (let
                                    ((result$2 r.0$2_0))
                                    (and
                                       (INV_REC_f__1_PRE add$1_0)
                                       (forall
                                          ((call$1_0 Int))
                                          (=>
                                             (INV_REC_f__1 add$1_0 call$1_0)
                                             (and
                                                (INV_REC_f__1_PRE call$1_0)
                                                (forall
                                                   ((call1$1_0 Int))
                                                   (=>
                                                      (INV_REC_f__1 call$1_0 call1$1_0)
                                                      (let
                                                         ((r.0$1_0 call1$1_0))
                                                         (let
                                                            ((result$1 r.0$1_0))
                                                            (INV_REC_f^f a$1_0_old x$2_0_old result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE a$1_0_old)
         (let
            ((a$1_0 a$1_0_old))
            (let
               ((cmp$1_0 (> a$1_0 100)))
               (=>
                  cmp$1_0
                  (let
                     ((sub$1_0 (- a$1_0 10)))
                     (let
                        ((r.0$1_0 sub$1_0))
                        (let
                           ((result$1 r.0$1_0))
                           (INV_REC_f__1 a$1_0_old result$1))))))))))
(assert
   (forall
      ((a$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE a$1_0_old)
         (let
            ((a$1_0 a$1_0_old))
            (let
               ((cmp$1_0 (> a$1_0 100)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((add$1_0 (+ a$1_0 11)))
                     (and
                        (INV_REC_f__1_PRE add$1_0)
                        (forall
                           ((call$1_0 Int))
                           (=>
                              (INV_REC_f__1 add$1_0 call$1_0)
                              (and
                                 (INV_REC_f__1_PRE call$1_0)
                                 (forall
                                    ((call1$1_0 Int))
                                    (=>
                                       (INV_REC_f__1 call$1_0 call1$1_0)
                                       (let
                                          ((r.0$1_0 call1$1_0))
                                          (let
                                             ((result$1 r.0$1_0))
                                             (INV_REC_f__1 a$1_0_old result$1))))))))))))))))
(assert
   (forall
      ((x$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE x$2_0_old)
         (let
            ((x$2_0 x$2_0_old))
            (let
               ((cmp$2_0 (< x$2_0 101)))
               (=>
                  cmp$2_0
                  (let
                     ((add$2_0 (+ 11 x$2_0)))
                     (and
                        (INV_REC_f__2_PRE add$2_0)
                        (forall
                           ((call$2_0 Int))
                           (=>
                              (INV_REC_f__2 add$2_0 call$2_0)
                              (and
                                 (INV_REC_f__2_PRE call$2_0)
                                 (forall
                                    ((call1$2_0 Int))
                                    (=>
                                       (INV_REC_f__2 call$2_0 call1$2_0)
                                       (let
                                          ((r.0$2_0 call1$2_0))
                                          (let
                                             ((result$2 r.0$2_0))
                                             (INV_REC_f__2 x$2_0_old result$2))))))))))))))))
(assert
   (forall
      ((x$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE x$2_0_old)
         (let
            ((x$2_0 x$2_0_old))
            (let
               ((cmp$2_0 (< x$2_0 101)))
               (=>
                  (not cmp$2_0)
                  (let
                     ((sub$2_0 (- x$2_0 10)))
                     (let
                        ((r.0$2_0 sub$2_0))
                        (let
                           ((result$2 r.0$2_0))
                           (INV_REC_f__2 x$2_0_old result$2))))))))))
(check-sat)
(get-model)
