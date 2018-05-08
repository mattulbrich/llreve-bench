;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((n$1_0 Int)
    (z$1_0 Int)
    (n$2_0 Int)
    (z$2_0 Int))
   Bool
   (and
      (= n$1_0 n$2_0)
      (= z$1_0 z$2_0)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
; :annot (INV_MAIN_42 i.0$1_0 n$1_0 i.0$2_0 n$2_0)
(declare-fun
   INV_MAIN_42
   (Int
    Int
    Int
    Int)
   Bool)
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
   INV_42
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42_PRE
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
   INV_42__1
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__1_PRE
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
(declare-fun
   INV_42__2
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__2_PRE
   (Int
    Int)
   Bool)
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (IN_INV n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((z$1_0 z$1_0_old)
                (cmp$1_0 (<= n$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((r.0$1_0 n$1_0))
                     (let
                        ((result$1 r.0$1_0)
                         (n$2_0 n$2_0_old))
                        (let
                           ((z$2_0 z$2_0_old)
                            (cmp$2_0 (<= n$2_0 0)))
                           (=>
                              (not cmp$2_0)
                              (let
                                 ((i.0$2_0 0))
                                 false)))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (IN_INV n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((z$1_0 z$1_0_old)
                (cmp$1_0 (<= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((i.0$1_0 0)
                      (n$2_0 n$2_0_old))
                     (let
                        ((z$2_0 z$2_0_old)
                         (cmp$2_0 (<= n$2_0 0)))
                        (=>
                           cmp$2_0
                           (let
                              ((r.0$2_0 n$2_0))
                              (let
                                 ((result$2 r.0$2_0))
                                 false)))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (IN_INV n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((z$1_0 z$1_0_old)
                (cmp$1_0 (<= n$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((r.0$1_0 n$1_0))
                     (let
                        ((result$1 r.0$1_0)
                         (n$2_0 n$2_0_old))
                        (let
                           ((z$2_0 z$2_0_old)
                            (cmp$2_0 (<= n$2_0 0)))
                           (=>
                              cmp$2_0
                              (let
                                 ((r.0$2_0 n$2_0))
                                 (let
                                    ((result$2 r.0$2_0))
                                    (OUT_INV result$1 result$2)))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (IN_INV n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((z$1_0 z$1_0_old)
                (cmp$1_0 (<= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((i.0$1_0 0)
                      (n$2_0 n$2_0_old))
                     (let
                        ((z$2_0 z$2_0_old)
                         (cmp$2_0 (<= n$2_0 0)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((i.0$2_0 0))
                              (INV_MAIN_42 i.0$1_0 n$1_0 i.0$2_0 n$2_0)))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((sub$1_0 (- n$1_0 1)))
               (let
                  ((cmp1$1_0 (< i.0$1_0 sub$1_0)))
                  (=>
                     (not cmp1$1_0)
                     (let
                        ((i.0$2_0 i.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((sub$2_0 (- n$2_0 1)))
                           (let
                              ((cmp1$2_0 (< i.0$2_0 sub$2_0)))
                              (=>
                                 cmp1$2_0
                                 (let
                                    ((add$2_0 (+ i.0$2_0 1)))
                                    (let
                                       ((i.0$2_0 add$2_0))
                                       (and
                                          (INV_REC_f__1_PRE i.0$1_0 0)
                                          (forall
                                             ((call2$1_0 Int))
                                             (=>
                                                (INV_REC_f__1 i.0$1_0 0 call2$1_0)
                                                (let
                                                   ((r.0$1_0 call2$1_0))
                                                   (let
                                                      ((result$1 r.0$1_0))
                                                      false))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((sub$1_0 (- n$1_0 1)))
               (let
                  ((cmp1$1_0 (< i.0$1_0 sub$1_0)))
                  (=>
                     cmp1$1_0
                     (let
                        ((add$1_0 (+ i.0$1_0 1)))
                        (let
                           ((i.0$1_0 add$1_0)
                            (i.0$2_0 i.0$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((sub$2_0 (- n$2_0 1)))
                              (let
                                 ((cmp1$2_0 (< i.0$2_0 sub$2_0)))
                                 (=>
                                    (not cmp1$2_0)
                                    (and
                                       (INV_REC_f__2_PRE i.0$2_0 0)
                                       (forall
                                          ((call2$2_0 Int))
                                          (=>
                                             (INV_REC_f__2 i.0$2_0 0 call2$2_0)
                                             (let
                                                ((r.0$2_0 call2$2_0))
                                                (let
                                                   ((result$2 r.0$2_0))
                                                   false)))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((sub$1_0 (- n$1_0 1)))
               (let
                  ((cmp1$1_0 (< i.0$1_0 sub$1_0)))
                  (=>
                     (not cmp1$1_0)
                     (let
                        ((i.0$2_0 i.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((sub$2_0 (- n$2_0 1)))
                           (let
                              ((cmp1$2_0 (< i.0$2_0 sub$2_0)))
                              (=>
                                 (not cmp1$2_0)
                                 (and
                                    (INV_REC_f^f_PRE i.0$1_0 0 i.0$2_0 0)
                                    (forall
                                       ((call2$1_0 Int)
                                        (call2$2_0 Int))
                                       (=>
                                          (INV_REC_f^f i.0$1_0 0 i.0$2_0 0 call2$1_0 call2$2_0)
                                          (let
                                             ((r.0$1_0 call2$1_0))
                                             (let
                                                ((result$1 r.0$1_0)
                                                 (r.0$2_0 call2$2_0))
                                                (let
                                                   ((result$2 r.0$2_0))
                                                   (OUT_INV result$1 result$2))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((sub$1_0 (- n$1_0 1)))
               (let
                  ((cmp1$1_0 (< i.0$1_0 sub$1_0)))
                  (=>
                     cmp1$1_0
                     (let
                        ((add$1_0 (+ i.0$1_0 1)))
                        (let
                           ((i.0$1_0 add$1_0)
                            (i.0$2_0 i.0$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((sub$2_0 (- n$2_0 1)))
                              (let
                                 ((cmp1$2_0 (< i.0$2_0 sub$2_0)))
                                 (=>
                                    cmp1$2_0
                                    (let
                                       ((add$2_0 (+ i.0$2_0 1)))
                                       (let
                                          ((i.0$2_0 add$2_0))
                                          (INV_MAIN_42 i.0$1_0 n$1_0 i.0$2_0 n$2_0)))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((z$1_0 z$1_0_old)
                (cmp$1_0 (<= n$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((r.0$1_0 n$1_0))
                     (let
                        ((result$1 r.0$1_0)
                         (n$2_0 n$2_0_old))
                        (let
                           ((z$2_0 z$2_0_old)
                            (cmp$2_0 (<= n$2_0 0)))
                           (=>
                              (not cmp$2_0)
                              (let
                                 ((i.0$2_0 0))
                                 false)))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((z$1_0 z$1_0_old)
                (cmp$1_0 (<= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((i.0$1_0 0)
                      (n$2_0 n$2_0_old))
                     (let
                        ((z$2_0 z$2_0_old)
                         (cmp$2_0 (<= n$2_0 0)))
                        (=>
                           cmp$2_0
                           (let
                              ((r.0$2_0 n$2_0))
                              (let
                                 ((result$2 r.0$2_0))
                                 false)))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((z$1_0 z$1_0_old)
                (cmp$1_0 (<= n$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((r.0$1_0 n$1_0))
                     (let
                        ((result$1 r.0$1_0)
                         (n$2_0 n$2_0_old))
                        (let
                           ((z$2_0 z$2_0_old)
                            (cmp$2_0 (<= n$2_0 0)))
                           (=>
                              cmp$2_0
                              (let
                                 ((r.0$2_0 n$2_0))
                                 (let
                                    ((result$2 r.0$2_0))
                                    (INV_REC_f^f n$1_0_old z$1_0_old n$2_0_old z$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((z$1_0 z$1_0_old)
                (cmp$1_0 (<= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((i.0$1_0 0)
                      (n$2_0 n$2_0_old))
                     (let
                        ((z$2_0 z$2_0_old)
                         (cmp$2_0 (<= n$2_0 0)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((i.0$2_0 0))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_42_PRE i.0$1_0 n$1_0 i.0$2_0 n$2_0)
                                    (=>
                                       (INV_42 i.0$1_0 n$1_0 i.0$2_0 n$2_0 result$1 result$2)
                                       (INV_REC_f^f n$1_0_old z$1_0_old n$2_0_old z$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((sub$1_0 (- n$1_0 1)))
               (let
                  ((cmp1$1_0 (< i.0$1_0 sub$1_0)))
                  (=>
                     (not cmp1$1_0)
                     (let
                        ((i.0$2_0 i.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((sub$2_0 (- n$2_0 1)))
                           (let
                              ((cmp1$2_0 (< i.0$2_0 sub$2_0)))
                              (=>
                                 cmp1$2_0
                                 (let
                                    ((add$2_0 (+ i.0$2_0 1)))
                                    (let
                                       ((i.0$2_0 add$2_0))
                                       (and
                                          (INV_REC_f__1_PRE i.0$1_0 0)
                                          (forall
                                             ((call2$1_0 Int))
                                             (=>
                                                (INV_REC_f__1 i.0$1_0 0 call2$1_0)
                                                (let
                                                   ((r.0$1_0 call2$1_0))
                                                   (let
                                                      ((result$1 r.0$1_0))
                                                      false))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((sub$1_0 (- n$1_0 1)))
               (let
                  ((cmp1$1_0 (< i.0$1_0 sub$1_0)))
                  (=>
                     cmp1$1_0
                     (let
                        ((add$1_0 (+ i.0$1_0 1)))
                        (let
                           ((i.0$1_0 add$1_0)
                            (i.0$2_0 i.0$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((sub$2_0 (- n$2_0 1)))
                              (let
                                 ((cmp1$2_0 (< i.0$2_0 sub$2_0)))
                                 (=>
                                    (not cmp1$2_0)
                                    (and
                                       (INV_REC_f__2_PRE i.0$2_0 0)
                                       (forall
                                          ((call2$2_0 Int))
                                          (=>
                                             (INV_REC_f__2 i.0$2_0 0 call2$2_0)
                                             (let
                                                ((r.0$2_0 call2$2_0))
                                                (let
                                                   ((result$2 r.0$2_0))
                                                   false)))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((sub$1_0 (- n$1_0 1)))
               (let
                  ((cmp1$1_0 (< i.0$1_0 sub$1_0)))
                  (=>
                     (not cmp1$1_0)
                     (let
                        ((i.0$2_0 i.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((sub$2_0 (- n$2_0 1)))
                           (let
                              ((cmp1$2_0 (< i.0$2_0 sub$2_0)))
                              (=>
                                 (not cmp1$2_0)
                                 (and
                                    (INV_REC_f^f_PRE i.0$1_0 0 i.0$2_0 0)
                                    (forall
                                       ((call2$1_0 Int)
                                        (call2$2_0 Int))
                                       (=>
                                          (INV_REC_f^f i.0$1_0 0 i.0$2_0 0 call2$1_0 call2$2_0)
                                          (let
                                             ((r.0$1_0 call2$1_0))
                                             (let
                                                ((result$1 r.0$1_0)
                                                 (r.0$2_0 call2$2_0))
                                                (let
                                                   ((result$2 r.0$2_0))
                                                   (INV_42 i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old result$1 result$2))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((sub$1_0 (- n$1_0 1)))
               (let
                  ((cmp1$1_0 (< i.0$1_0 sub$1_0)))
                  (=>
                     cmp1$1_0
                     (let
                        ((add$1_0 (+ i.0$1_0 1)))
                        (let
                           ((i.0$1_0 add$1_0)
                            (i.0$2_0 i.0$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((sub$2_0 (- n$2_0 1)))
                              (let
                                 ((cmp1$2_0 (< i.0$2_0 sub$2_0)))
                                 (=>
                                    cmp1$2_0
                                    (let
                                       ((add$2_0 (+ i.0$2_0 1)))
                                       (let
                                          ((i.0$2_0 add$2_0))
                                          (forall
                                             ((result$1 Int)
                                              (result$2 Int))
                                             (and
                                                (INV_42_PRE i.0$1_0 n$1_0 i.0$2_0 n$2_0)
                                                (=>
                                                   (INV_42 i.0$1_0 n$1_0 i.0$2_0 n$2_0 result$1 result$2)
                                                   (INV_42 i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old result$1 result$2))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE n$1_0_old z$1_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((z$1_0 z$1_0_old)
                (cmp$1_0 (<= n$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((r.0$1_0 n$1_0))
                     (let
                        ((result$1 r.0$1_0))
                        (INV_REC_f__1 n$1_0_old z$1_0_old result$1)))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE n$1_0_old z$1_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((z$1_0 z$1_0_old)
                (cmp$1_0 (<= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((i.0$1_0 0))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_42__1 i.0$1_0 n$1_0 result$1)
                           (INV_REC_f__1 n$1_0_old z$1_0_old result$1))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE i.0$1_0_old n$1_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((sub$1_0 (- n$1_0 1)))
               (let
                  ((cmp1$1_0 (< i.0$1_0 sub$1_0)))
                  (=>
                     (not cmp1$1_0)
                     (and
                        (INV_REC_f__1_PRE i.0$1_0 0)
                        (forall
                           ((call2$1_0 Int))
                           (=>
                              (INV_REC_f__1 i.0$1_0 0 call2$1_0)
                              (let
                                 ((r.0$1_0 call2$1_0))
                                 (let
                                    ((result$1 r.0$1_0))
                                    (INV_42__1 i.0$1_0_old n$1_0_old result$1)))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE i.0$1_0_old n$1_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((sub$1_0 (- n$1_0 1)))
               (let
                  ((cmp1$1_0 (< i.0$1_0 sub$1_0)))
                  (=>
                     cmp1$1_0
                     (let
                        ((add$1_0 (+ i.0$1_0 1)))
                        (let
                           ((i.0$1_0 add$1_0))
                           (forall
                              ((result$1 Int))
                              (=>
                                 (INV_42__1 i.0$1_0 n$1_0 result$1)
                                 (INV_42__1 i.0$1_0_old n$1_0_old result$1))))))))))))
(assert
   (forall
      ((n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE n$2_0_old z$2_0_old)
         (let
            ((n$2_0 n$2_0_old))
            (let
               ((z$2_0 z$2_0_old)
                (cmp$2_0 (<= n$2_0 0)))
               (=>
                  cmp$2_0
                  (let
                     ((r.0$2_0 n$2_0))
                     (let
                        ((result$2 r.0$2_0))
                        (INV_REC_f__2 n$2_0_old z$2_0_old result$2)))))))))
(assert
   (forall
      ((n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE n$2_0_old z$2_0_old)
         (let
            ((n$2_0 n$2_0_old))
            (let
               ((z$2_0 z$2_0_old)
                (cmp$2_0 (<= n$2_0 0)))
               (=>
                  (not cmp$2_0)
                  (let
                     ((i.0$2_0 0))
                     (forall
                        ((result$2 Int))
                        (=>
                           (INV_42__2 i.0$2_0 n$2_0 result$2)
                           (INV_REC_f__2 n$2_0_old z$2_0_old result$2))))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42__2_PRE i.0$2_0_old n$2_0_old)
         (let
            ((i.0$2_0 i.0$2_0_old)
             (n$2_0 n$2_0_old))
            (let
               ((sub$2_0 (- n$2_0 1)))
               (let
                  ((cmp1$2_0 (< i.0$2_0 sub$2_0)))
                  (=>
                     (not cmp1$2_0)
                     (and
                        (INV_REC_f__2_PRE i.0$2_0 0)
                        (forall
                           ((call2$2_0 Int))
                           (=>
                              (INV_REC_f__2 i.0$2_0 0 call2$2_0)
                              (let
                                 ((r.0$2_0 call2$2_0))
                                 (let
                                    ((result$2 r.0$2_0))
                                    (INV_42__2 i.0$2_0_old n$2_0_old result$2)))))))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42__2_PRE i.0$2_0_old n$2_0_old)
         (let
            ((i.0$2_0 i.0$2_0_old)
             (n$2_0 n$2_0_old))
            (let
               ((sub$2_0 (- n$2_0 1)))
               (let
                  ((cmp1$2_0 (< i.0$2_0 sub$2_0)))
                  (=>
                     cmp1$2_0
                     (let
                        ((add$2_0 (+ i.0$2_0 1)))
                        (let
                           ((i.0$2_0 add$2_0))
                           (forall
                              ((result$2 Int))
                              (=>
                                 (INV_42__2 i.0$2_0 n$2_0 result$2)
                                 (INV_42__2 i.0$2_0_old n$2_0_old result$2))))))))))))
(check-sat)
(get-model)
