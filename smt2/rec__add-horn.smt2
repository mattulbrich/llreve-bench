;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((i$1_0 Int)
    (j$1_0 Int)
    (i$2_0 Int)
    (j$2_0 Int))
   Bool
   (and
      (= i$1_0 i$2_0)
      (= j$1_0 j$2_0)))
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
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f^f_PRE
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__2
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__2_PRE
   (Int
    Int)
   Bool)
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (IN_INV i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((r.0$1_0 j$1_0))
                     (let
                        ((result$1 r.0$1_0)
                         (i$2_0 i$2_0_old)
                         (j$2_0 j$2_0_old))
                        (=>
                           (= i$2_0 0)
                           (let
                              ((r.1$2_0 j$2_0))
                              (let
                                 ((result$2 r.1$2_0))
                                 (OUT_INV result$1 result$2))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (IN_INV i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((r.0$1_0 j$1_0))
                     (let
                        ((result$1 r.0$1_0)
                         (i$2_0 i$2_0_old)
                         (j$2_0 j$2_0_old))
                        (=>
                           (= i$2_0 1)
                           (let
                              ((add$2_0 (+ j$2_0 1)))
                              (let
                                 ((r.1$2_0 add$2_0))
                                 (let
                                    ((result$2 r.1$2_0))
                                    (OUT_INV result$1 result$2)))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (IN_INV i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((r.0$1_0 j$1_0))
                     (let
                        ((result$1 r.0$1_0)
                         (i$2_0 i$2_0_old)
                         (j$2_0 j$2_0_old))
                        (=>
                           (distinct 0 1 i$2_0)
                           (let
                              ((sub$2_0 (- i$2_0 1))
                               (add4$2_0 (+ j$2_0 1)))
                              (and
                                 (INV_REC_f__2_PRE sub$2_0 add4$2_0)
                                 (forall
                                    ((call$2_0 Int))
                                    (=>
                                       (INV_REC_f__2 sub$2_0 add4$2_0 call$2_0)
                                       (let
                                          ((r.1$2_0 call$2_0))
                                          (let
                                             ((result$2 r.1$2_0))
                                             (OUT_INV result$1 result$2))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (IN_INV i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((sub$1_0 (- i$1_0 1))
                      (add$1_0 (+ j$1_0 1))
                      (i$2_0 i$2_0_old)
                      (j$2_0 j$2_0_old))
                     (=>
                        (= i$2_0 0)
                        (let
                           ((r.1$2_0 j$2_0))
                           (let
                              ((result$2 r.1$2_0))
                              (and
                                 (INV_REC_f__1_PRE sub$1_0 add$1_0)
                                 (forall
                                    ((call$1_0 Int))
                                    (=>
                                       (INV_REC_f__1 sub$1_0 add$1_0 call$1_0)
                                       (let
                                          ((r.0$1_0 call$1_0))
                                          (let
                                             ((result$1 r.0$1_0))
                                             (OUT_INV result$1 result$2))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (IN_INV i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((sub$1_0 (- i$1_0 1))
                      (add$1_0 (+ j$1_0 1))
                      (i$2_0 i$2_0_old)
                      (j$2_0 j$2_0_old))
                     (=>
                        (= i$2_0 1)
                        (let
                           ((add$2_0 (+ j$2_0 1)))
                           (let
                              ((r.1$2_0 add$2_0))
                              (let
                                 ((result$2 r.1$2_0))
                                 (and
                                    (INV_REC_f__1_PRE sub$1_0 add$1_0)
                                    (forall
                                       ((call$1_0 Int))
                                       (=>
                                          (INV_REC_f__1 sub$1_0 add$1_0 call$1_0)
                                          (let
                                             ((r.0$1_0 call$1_0))
                                             (let
                                                ((result$1 r.0$1_0))
                                                (OUT_INV result$1 result$2)))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (IN_INV i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((sub$1_0 (- i$1_0 1))
                      (add$1_0 (+ j$1_0 1))
                      (i$2_0 i$2_0_old)
                      (j$2_0 j$2_0_old))
                     (=>
                        (distinct 0 1 i$2_0)
                        (let
                           ((sub$2_0 (- i$2_0 1))
                            (add4$2_0 (+ j$2_0 1)))
                           (and
                              (INV_REC_f^f_PRE sub$1_0 add$1_0 sub$2_0 add4$2_0)
                              (forall
                                 ((call$1_0 Int)
                                  (call$2_0 Int))
                                 (=>
                                    (INV_REC_f^f sub$1_0 add$1_0 sub$2_0 add4$2_0 call$1_0 call$2_0)
                                    (let
                                       ((r.0$1_0 call$1_0))
                                       (let
                                          ((result$1 r.0$1_0)
                                           (r.1$2_0 call$2_0))
                                          (let
                                             ((result$2 r.1$2_0))
                                             (OUT_INV result$1 result$2))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((r.0$1_0 j$1_0))
                     (let
                        ((result$1 r.0$1_0)
                         (i$2_0 i$2_0_old)
                         (j$2_0 j$2_0_old))
                        (=>
                           (= i$2_0 0)
                           (let
                              ((r.1$2_0 j$2_0))
                              (let
                                 ((result$2 r.1$2_0))
                                 (INV_REC_f^f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((r.0$1_0 j$1_0))
                     (let
                        ((result$1 r.0$1_0)
                         (i$2_0 i$2_0_old)
                         (j$2_0 j$2_0_old))
                        (=>
                           (= i$2_0 1)
                           (let
                              ((add$2_0 (+ j$2_0 1)))
                              (let
                                 ((r.1$2_0 add$2_0))
                                 (let
                                    ((result$2 r.1$2_0))
                                    (INV_REC_f^f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((r.0$1_0 j$1_0))
                     (let
                        ((result$1 r.0$1_0)
                         (i$2_0 i$2_0_old)
                         (j$2_0 j$2_0_old))
                        (=>
                           (distinct 0 1 i$2_0)
                           (let
                              ((sub$2_0 (- i$2_0 1))
                               (add4$2_0 (+ j$2_0 1)))
                              (and
                                 (INV_REC_f__2_PRE sub$2_0 add4$2_0)
                                 (forall
                                    ((call$2_0 Int))
                                    (=>
                                       (INV_REC_f__2 sub$2_0 add4$2_0 call$2_0)
                                       (let
                                          ((r.1$2_0 call$2_0))
                                          (let
                                             ((result$2 r.1$2_0))
                                             (INV_REC_f^f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((sub$1_0 (- i$1_0 1))
                      (add$1_0 (+ j$1_0 1))
                      (i$2_0 i$2_0_old)
                      (j$2_0 j$2_0_old))
                     (=>
                        (= i$2_0 0)
                        (let
                           ((r.1$2_0 j$2_0))
                           (let
                              ((result$2 r.1$2_0))
                              (and
                                 (INV_REC_f__1_PRE sub$1_0 add$1_0)
                                 (forall
                                    ((call$1_0 Int))
                                    (=>
                                       (INV_REC_f__1 sub$1_0 add$1_0 call$1_0)
                                       (let
                                          ((r.0$1_0 call$1_0))
                                          (let
                                             ((result$1 r.0$1_0))
                                             (INV_REC_f^f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((sub$1_0 (- i$1_0 1))
                      (add$1_0 (+ j$1_0 1))
                      (i$2_0 i$2_0_old)
                      (j$2_0 j$2_0_old))
                     (=>
                        (= i$2_0 1)
                        (let
                           ((add$2_0 (+ j$2_0 1)))
                           (let
                              ((r.1$2_0 add$2_0))
                              (let
                                 ((result$2 r.1$2_0))
                                 (and
                                    (INV_REC_f__1_PRE sub$1_0 add$1_0)
                                    (forall
                                       ((call$1_0 Int))
                                       (=>
                                          (INV_REC_f__1 sub$1_0 add$1_0 call$1_0)
                                          (let
                                             ((r.0$1_0 call$1_0))
                                             (let
                                                ((result$1 r.0$1_0))
                                                (INV_REC_f^f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2)))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((sub$1_0 (- i$1_0 1))
                      (add$1_0 (+ j$1_0 1))
                      (i$2_0 i$2_0_old)
                      (j$2_0 j$2_0_old))
                     (=>
                        (distinct 0 1 i$2_0)
                        (let
                           ((sub$2_0 (- i$2_0 1))
                            (add4$2_0 (+ j$2_0 1)))
                           (and
                              (INV_REC_f^f_PRE sub$1_0 add$1_0 sub$2_0 add4$2_0)
                              (forall
                                 ((call$1_0 Int)
                                  (call$2_0 Int))
                                 (=>
                                    (INV_REC_f^f sub$1_0 add$1_0 sub$2_0 add4$2_0 call$1_0 call$2_0)
                                    (let
                                       ((r.0$1_0 call$1_0))
                                       (let
                                          ((result$1 r.0$1_0)
                                           (r.1$2_0 call$2_0))
                                          (let
                                             ((result$2 r.1$2_0))
                                             (INV_REC_f^f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE i$1_0_old j$1_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((r.0$1_0 j$1_0))
                     (let
                        ((result$1 r.0$1_0))
                        (INV_REC_f__1 i$1_0_old j$1_0_old result$1)))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE i$1_0_old j$1_0_old)
         (let
            ((i$1_0 i$1_0_old))
            (let
               ((j$1_0 j$1_0_old)
                (cmp$1_0 (= i$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((sub$1_0 (- i$1_0 1))
                      (add$1_0 (+ j$1_0 1)))
                     (and
                        (INV_REC_f__1_PRE sub$1_0 add$1_0)
                        (forall
                           ((call$1_0 Int))
                           (=>
                              (INV_REC_f__1 sub$1_0 add$1_0 call$1_0)
                              (let
                                 ((r.0$1_0 call$1_0))
                                 (let
                                    ((result$1 r.0$1_0))
                                    (INV_REC_f__1 i$1_0_old j$1_0_old result$1)))))))))))))
(assert
   (forall
      ((i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE i$2_0_old j$2_0_old)
         (let
            ((i$2_0 i$2_0_old)
             (j$2_0 j$2_0_old))
            (=>
               (= i$2_0 0)
               (let
                  ((r.1$2_0 j$2_0))
                  (let
                     ((result$2 r.1$2_0))
                     (INV_REC_f__2 i$2_0_old j$2_0_old result$2))))))))
(assert
   (forall
      ((i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE i$2_0_old j$2_0_old)
         (let
            ((i$2_0 i$2_0_old)
             (j$2_0 j$2_0_old))
            (=>
               (= i$2_0 1)
               (let
                  ((add$2_0 (+ j$2_0 1)))
                  (let
                     ((r.1$2_0 add$2_0))
                     (let
                        ((result$2 r.1$2_0))
                        (INV_REC_f__2 i$2_0_old j$2_0_old result$2)))))))))
(assert
   (forall
      ((i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE i$2_0_old j$2_0_old)
         (let
            ((i$2_0 i$2_0_old)
             (j$2_0 j$2_0_old))
            (=>
               (distinct 0 1 i$2_0)
               (let
                  ((sub$2_0 (- i$2_0 1))
                   (add4$2_0 (+ j$2_0 1)))
                  (and
                     (INV_REC_f__2_PRE sub$2_0 add4$2_0)
                     (forall
                        ((call$2_0 Int))
                        (=>
                           (INV_REC_f__2 sub$2_0 add4$2_0 call$2_0)
                           (let
                              ((r.1$2_0 call$2_0))
                              (let
                                 ((result$2 r.1$2_0))
                                 (INV_REC_f__2 i$2_0_old j$2_0_old result$2))))))))))))
(check-sat)
(get-model)
