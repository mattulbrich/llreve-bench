;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((m$1_0 Int)
    (m$2_0 Int))
   Bool
   (= m$1_0 m$2_0))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
(declare-fun
   INV_REC_tr^tr
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_tr^tr_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_42
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_tr__1
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_tr__1_PRE
   (Int)
   Bool)
(declare-fun
   INV_42__1
   (Int
    Int)
   Bool)
(declare-fun
   INV_42__1_PRE
   (Int)
   Bool)
(declare-fun
   INV_REC_tr__2
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_tr__2_PRE
   (Int)
   Bool)
(declare-fun
   INV_42__2
   (Int
    Int)
   Bool)
(declare-fun
   INV_42__2_PRE
   (Int)
   Bool)
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (IN_INV m$1_0_old m$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((cmp$1_0 (> m$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((sub$1_0 (- m$1_0 1))
                      (m$2_0 m$2_0_old))
                     (let
                        ((cmp$2_0 (> m$2_0 0)))
                        (=>
                           cmp$2_0
                           (let
                              ((sub$2_0 (- m$2_0 1)))
                              (and
                                 (INV_REC_tr^tr_PRE sub$1_0 sub$2_0)
                                 (forall
                                    ((call$1_0 Int)
                                     (call$2_0 Int))
                                    (=>
                                       (INV_REC_tr^tr sub$1_0 sub$2_0 call$1_0 call$2_0)
                                       (let
                                          ((add$1_0 (+ call$1_0 m$1_0)))
                                          (let
                                             ((result.0$1_0 add$1_0))
                                             (let
                                                ((result$1 result.0$1_0)
                                                 (cmp1$2_0 (>= call$2_0 0))
                                                 (add$2_0 (+ call$2_0 m$2_0)))
                                                (let
                                                   ((add.call$2_0 (ite cmp1$2_0 add$2_0 call$2_0)))
                                                   (let
                                                      ((result.1$2_0 add.call$2_0))
                                                      (let
                                                         ((result$2 result.1$2_0))
                                                         (OUT_INV result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (IN_INV m$1_0_old m$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((cmp$1_0 (> m$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((sub$1_0 (- m$1_0 1))
                      (m$2_0 m$2_0_old))
                     (let
                        ((cmp$2_0 (> m$2_0 0)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((result.1$2_0 0))
                              (let
                                 ((result$2 result.1$2_0))
                                 (and
                                    (INV_REC_tr__1_PRE sub$1_0)
                                    (forall
                                       ((call$1_0 Int))
                                       (=>
                                          (INV_REC_tr__1 sub$1_0 call$1_0)
                                          (let
                                             ((add$1_0 (+ call$1_0 m$1_0)))
                                             (let
                                                ((result.0$1_0 add$1_0))
                                                (let
                                                   ((result$1 result.0$1_0))
                                                   (OUT_INV result$1 result$2))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (IN_INV m$1_0_old m$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((cmp$1_0 (> m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result.0$1_0 0))
                     (let
                        ((result$1 result.0$1_0)
                         (m$2_0 m$2_0_old))
                        (let
                           ((cmp$2_0 (> m$2_0 0)))
                           (=>
                              cmp$2_0
                              (let
                                 ((sub$2_0 (- m$2_0 1)))
                                 (and
                                    (INV_REC_tr__2_PRE sub$2_0)
                                    (forall
                                       ((call$2_0 Int))
                                       (=>
                                          (INV_REC_tr__2 sub$2_0 call$2_0)
                                          (let
                                             ((cmp1$2_0 (>= call$2_0 0))
                                              (add$2_0 (+ call$2_0 m$2_0)))
                                             (let
                                                ((add.call$2_0 (ite cmp1$2_0 add$2_0 call$2_0)))
                                                (let
                                                   ((result.1$2_0 add.call$2_0))
                                                   (let
                                                      ((result$2 result.1$2_0))
                                                      (OUT_INV result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (IN_INV m$1_0_old m$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((cmp$1_0 (> m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result.0$1_0 0))
                     (let
                        ((result$1 result.0$1_0)
                         (m$2_0 m$2_0_old))
                        (let
                           ((cmp$2_0 (> m$2_0 0)))
                           (=>
                              (not cmp$2_0)
                              (let
                                 ((result.1$2_0 0))
                                 (let
                                    ((result$2 result.1$2_0))
                                    (OUT_INV result$1 result$2)))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_tr^tr_PRE n$1_0_old n$2_0_old)
         (let
            ((n$1_0 n$1_0_old)
             (n$2_0 n$2_0_old))
            (forall
               ((result$1 Int)
                (result$2 Int))
               (and
                  (INV_42_PRE n$1_0 n$2_0)
                  (=>
                     (INV_42 n$1_0 n$2_0 result$1 result$2)
                     (INV_REC_tr^tr n$1_0_old n$2_0_old result$1 result$2))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE n$1_0_old n$2_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((cmp$1_0 (< 0 n$1_0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 0)
                      (n$2_0 n$2_0_old))
                     (let
                        ((cmp$2_0 (< 0 n$2_0)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((result$2 0))
                              (INV_42 n$1_0_old n$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE n$1_0_old n$2_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((cmp$1_0 (< 0 n$1_0)))
               (=>
                  cmp$1_0
                  (let
                     ((n$2_0 n$2_0_old))
                     (let
                        ((cmp$2_0 (< 0 n$2_0)))
                        (=>
                           cmp$2_0
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_42_PRE n$1_0 n$2_0)
                                 (=>
                                    (INV_42 n$1_0 n$2_0 result$1 result$2)
                                    (INV_42 n$1_0_old n$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE n$1_0_old n$2_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((cmp$1_0 (< 0 n$1_0)))
               (=>
                  cmp$1_0
                  (=>
                     (let
                        ((n$2_0 n$2_0_old))
                        (let
                           ((cmp$2_0 (< 0 n$2_0)))
                           (not cmp$2_0)))
                     (forall
                        ((result$1 Int)
                         (result$2 Int))
                        (and
                           (INV_42_PRE n$1_0 n$2_0_old)
                           (=>
                              (INV_42 n$1_0 n$2_0_old result$1 result$2)
                              (INV_42 n$1_0_old n$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE n$1_0_old n$2_0_old)
         (let
            ((n$2_0 n$2_0_old))
            (let
               ((cmp$2_0 (< 0 n$2_0)))
               (=>
                  cmp$2_0
                  (=>
                     (let
                        ((n$1_0 n$1_0_old))
                        (let
                           ((cmp$1_0 (< 0 n$1_0)))
                           (not cmp$1_0)))
                     (forall
                        ((result$1 Int)
                         (result$2 Int))
                        (and
                           (INV_42_PRE n$1_0_old n$2_0)
                           (=>
                              (INV_42 n$1_0_old n$2_0 result$1 result$2)
                              (INV_42 n$1_0_old n$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((n$1_0_old Int))
      (=>
         (INV_REC_tr__1_PRE n$1_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (forall
               ((result$1 Int))
               (=>
                  (INV_42__1 n$1_0 result$1)
                  (INV_REC_tr__1 n$1_0_old result$1)))))))
(assert
   (forall
      ((n$1_0_old Int))
      (=>
         (INV_42__1_PRE n$1_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((cmp$1_0 (< 0 n$1_0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 0))
                     (INV_42__1 n$1_0_old result$1))))))))
(assert
   (forall
      ((n$1_0_old Int))
      (=>
         (INV_42__1_PRE n$1_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((cmp$1_0 (< 0 n$1_0)))
               (=>
                  cmp$1_0
                  (forall
                     ((result$1 Int))
                     (=>
                        (INV_42__1 n$1_0 result$1)
                        (INV_42__1 n$1_0_old result$1)))))))))
(assert
   (forall
      ((n$2_0_old Int))
      (=>
         (INV_REC_tr__2_PRE n$2_0_old)
         (let
            ((n$2_0 n$2_0_old))
            (forall
               ((result$2 Int))
               (=>
                  (INV_42__2 n$2_0 result$2)
                  (INV_REC_tr__2 n$2_0_old result$2)))))))
(assert
   (forall
      ((n$2_0_old Int))
      (=>
         (INV_42__2_PRE n$2_0_old)
         (let
            ((n$2_0 n$2_0_old))
            (let
               ((cmp$2_0 (< 0 n$2_0)))
               (=>
                  (not cmp$2_0)
                  (let
                     ((result$2 0))
                     (INV_42__2 n$2_0_old result$2))))))))
(assert
   (forall
      ((n$2_0_old Int))
      (=>
         (INV_42__2_PRE n$2_0_old)
         (let
            ((n$2_0 n$2_0_old))
            (let
               ((cmp$2_0 (< 0 n$2_0)))
               (=>
                  cmp$2_0
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_42__2 n$2_0 result$2)
                        (INV_42__2 n$2_0_old result$2)))))))))
(check-sat)
(get-model)
