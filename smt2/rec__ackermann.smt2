;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((m$1_0 Int)
    (n$1_0 Int)
    (m$2_0 Int)
    (n$2_0 Int))
   Bool
   (and
      (= m$1_0 m$2_0)
      (= n$1_0 n$2_0)))
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
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((add$1_0 (+ n$1_0 1)))
                     (let
                        ((r.1$1_0 add$1_0))
                        (let
                           ((result$1 r.1$1_0)
                            (m$2_0 m$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((cmp$2_0 (> m$2_0 0))
                               (cmp1$2_0 (= n$2_0 0)))
                              (let
                                 ((or.cond$2_0 (and
                                                   cmp$2_0
                                                   cmp1$2_0)))
                                 (=>
                                    or.cond$2_0
                                    (let
                                       ((sub$2_0 (- m$2_0 1)))
                                       (and
                                          (INV_REC_f__2_PRE sub$2_0 1)
                                          (forall
                                             ((call$2_0 Int))
                                             (=>
                                                (INV_REC_f__2 sub$2_0 1 call$2_0)
                                                (let
                                                   ((r.1$2_0 call$2_0))
                                                   (let
                                                      ((result$2 r.1$2_0))
                                                      (OUT_INV result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((add$1_0 (+ n$1_0 1)))
                     (let
                        ((r.1$1_0 add$1_0))
                        (let
                           ((result$1 r.1$1_0)
                            (m$2_0 m$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((cmp$2_0 (> m$2_0 0))
                               (cmp1$2_0 (= n$2_0 0)))
                              (let
                                 ((or.cond$2_0 (and
                                                   cmp$2_0
                                                   cmp1$2_0)))
                                 (=>
                                    (not or.cond$2_0)
                                    (let
                                       ((cmp2$2_0 (= m$2_0 0)))
                                       (=>
                                          cmp2$2_0
                                          (let
                                             ((add$2_0 (+ n$2_0 1)))
                                             (let
                                                ((r.1$2_0 add$2_0))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (OUT_INV result$1 result$2))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((add$1_0 (+ n$1_0 1)))
                     (let
                        ((r.1$1_0 add$1_0))
                        (let
                           ((result$1 r.1$1_0)
                            (m$2_0 m$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((cmp$2_0 (> m$2_0 0))
                               (cmp1$2_0 (= n$2_0 0)))
                              (let
                                 ((or.cond$2_0 (and
                                                   cmp$2_0
                                                   cmp1$2_0)))
                                 (=>
                                    (not or.cond$2_0)
                                    (let
                                       ((cmp2$2_0 (= m$2_0 0)))
                                       (=>
                                          (not cmp2$2_0)
                                          (let
                                             ((sub5$2_0 (- n$2_0 1)))
                                             (and
                                                (INV_REC_f__2_PRE m$2_0 sub5$2_0)
                                                (forall
                                                   ((call6$2_0 Int))
                                                   (=>
                                                      (INV_REC_f__2 m$2_0 sub5$2_0 call6$2_0)
                                                      (let
                                                         ((sub7$2_0 (- m$2_0 1)))
                                                         (and
                                                            (INV_REC_f__2_PRE sub7$2_0 call6$2_0)
                                                            (forall
                                                               ((call8$2_0 Int))
                                                               (=>
                                                                  (INV_REC_f__2 sub7$2_0 call6$2_0 call8$2_0)
                                                                  (let
                                                                     ((r.1$2_0 call8$2_0))
                                                                     (let
                                                                        ((result$2 r.1$2_0))
                                                                        (OUT_INV result$1 result$2)))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           or.cond$1_0
                           (let
                              ((call6.sink$1_0 1)
                               (sub7$1_0 (- m$1_0 1))
                               (m$2_0 m$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((cmp$2_0 (> m$2_0 0))
                                  (cmp1$2_0 (= n$2_0 0)))
                                 (let
                                    ((or.cond$2_0 (and
                                                      cmp$2_0
                                                      cmp1$2_0)))
                                    (=>
                                       or.cond$2_0
                                       (let
                                          ((sub$2_0 (- m$2_0 1)))
                                          (and
                                             (INV_REC_f^f_PRE sub7$1_0 call6.sink$1_0 sub$2_0 1)
                                             (forall
                                                ((call8$1_0 Int)
                                                 (call$2_0 Int))
                                                (=>
                                                   (INV_REC_f^f sub7$1_0 call6.sink$1_0 sub$2_0 1 call8$1_0 call$2_0)
                                                   (let
                                                      ((r.1$1_0 call8$1_0))
                                                      (let
                                                         ((result$1 r.1$1_0)
                                                          (r.1$2_0 call$2_0))
                                                         (let
                                                            ((result$2 r.1$2_0))
                                                            (OUT_INV result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           or.cond$1_0
                           (let
                              ((call6.sink$1_0 1)
                               (sub7$1_0 (- m$1_0 1))
                               (m$2_0 m$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((cmp$2_0 (> m$2_0 0))
                                  (cmp1$2_0 (= n$2_0 0)))
                                 (let
                                    ((or.cond$2_0 (and
                                                      cmp$2_0
                                                      cmp1$2_0)))
                                    (=>
                                       (not or.cond$2_0)
                                       (let
                                          ((cmp2$2_0 (= m$2_0 0)))
                                          (=>
                                             cmp2$2_0
                                             (let
                                                ((add$2_0 (+ n$2_0 1)))
                                                (let
                                                   ((r.1$2_0 add$2_0))
                                                   (let
                                                      ((result$2 r.1$2_0))
                                                      (and
                                                         (INV_REC_f__1_PRE sub7$1_0 call6.sink$1_0)
                                                         (forall
                                                            ((call8$1_0 Int))
                                                            (=>
                                                               (INV_REC_f__1 sub7$1_0 call6.sink$1_0 call8$1_0)
                                                               (let
                                                                  ((r.1$1_0 call8$1_0))
                                                                  (let
                                                                     ((result$1 r.1$1_0))
                                                                     (OUT_INV result$1 result$2))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           or.cond$1_0
                           (let
                              ((call6.sink$1_0 1)
                               (sub7$1_0 (- m$1_0 1))
                               (m$2_0 m$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((cmp$2_0 (> m$2_0 0))
                                  (cmp1$2_0 (= n$2_0 0)))
                                 (let
                                    ((or.cond$2_0 (and
                                                      cmp$2_0
                                                      cmp1$2_0)))
                                    (=>
                                       (not or.cond$2_0)
                                       (let
                                          ((cmp2$2_0 (= m$2_0 0)))
                                          (=>
                                             (not cmp2$2_0)
                                             (let
                                                ((sub5$2_0 (- n$2_0 1)))
                                                (and
                                                   (INV_REC_f__2_PRE m$2_0 sub5$2_0)
                                                   (forall
                                                      ((call6$2_0 Int))
                                                      (=>
                                                         (INV_REC_f__2 m$2_0 sub5$2_0 call6$2_0)
                                                         (let
                                                            ((sub7$2_0 (- m$2_0 1)))
                                                            (and
                                                               (INV_REC_f^f_PRE sub7$1_0 call6.sink$1_0 sub7$2_0 call6$2_0)
                                                               (forall
                                                                  ((call8$1_0 Int)
                                                                   (call8$2_0 Int))
                                                                  (=>
                                                                     (INV_REC_f^f sub7$1_0 call6.sink$1_0 sub7$2_0 call6$2_0 call8$1_0 call8$2_0)
                                                                     (let
                                                                        ((r.1$1_0 call8$1_0))
                                                                        (let
                                                                           ((result$1 r.1$1_0)
                                                                            (r.1$2_0 call8$2_0))
                                                                           (let
                                                                              ((result$2 r.1$2_0))
                                                                              (OUT_INV result$1 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           (not or.cond$1_0)
                           (let
                              ((sub5$1_0 (- n$1_0 1))
                               (m$2_0 m$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((cmp$2_0 (> m$2_0 0))
                                  (cmp1$2_0 (= n$2_0 0)))
                                 (let
                                    ((or.cond$2_0 (and
                                                      cmp$2_0
                                                      cmp1$2_0)))
                                    (=>
                                       or.cond$2_0
                                       (let
                                          ((sub$2_0 (- m$2_0 1)))
                                          (and
                                             (INV_REC_f__1_PRE m$1_0 sub5$1_0)
                                             (forall
                                                ((call6$1_0 Int))
                                                (=>
                                                   (INV_REC_f__1 m$1_0 sub5$1_0 call6$1_0)
                                                   (let
                                                      ((call6.sink$1_0 call6$1_0)
                                                       (sub7$1_0 (- m$1_0 1)))
                                                      (and
                                                         (INV_REC_f^f_PRE sub7$1_0 call6.sink$1_0 sub$2_0 1)
                                                         (forall
                                                            ((call8$1_0 Int)
                                                             (call$2_0 Int))
                                                            (=>
                                                               (INV_REC_f^f sub7$1_0 call6.sink$1_0 sub$2_0 1 call8$1_0 call$2_0)
                                                               (let
                                                                  ((r.1$1_0 call8$1_0))
                                                                  (let
                                                                     ((result$1 r.1$1_0)
                                                                      (r.1$2_0 call$2_0))
                                                                     (let
                                                                        ((result$2 r.1$2_0))
                                                                        (OUT_INV result$1 result$2)))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           (not or.cond$1_0)
                           (let
                              ((sub5$1_0 (- n$1_0 1))
                               (m$2_0 m$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((cmp$2_0 (> m$2_0 0))
                                  (cmp1$2_0 (= n$2_0 0)))
                                 (let
                                    ((or.cond$2_0 (and
                                                      cmp$2_0
                                                      cmp1$2_0)))
                                    (=>
                                       (not or.cond$2_0)
                                       (let
                                          ((cmp2$2_0 (= m$2_0 0)))
                                          (=>
                                             cmp2$2_0
                                             (let
                                                ((add$2_0 (+ n$2_0 1)))
                                                (let
                                                   ((r.1$2_0 add$2_0))
                                                   (let
                                                      ((result$2 r.1$2_0))
                                                      (and
                                                         (INV_REC_f__1_PRE m$1_0 sub5$1_0)
                                                         (forall
                                                            ((call6$1_0 Int))
                                                            (=>
                                                               (INV_REC_f__1 m$1_0 sub5$1_0 call6$1_0)
                                                               (let
                                                                  ((call6.sink$1_0 call6$1_0)
                                                                   (sub7$1_0 (- m$1_0 1)))
                                                                  (and
                                                                     (INV_REC_f__1_PRE sub7$1_0 call6.sink$1_0)
                                                                     (forall
                                                                        ((call8$1_0 Int))
                                                                        (=>
                                                                           (INV_REC_f__1 sub7$1_0 call6.sink$1_0 call8$1_0)
                                                                           (let
                                                                              ((r.1$1_0 call8$1_0))
                                                                              (let
                                                                                 ((result$1 r.1$1_0))
                                                                                 (OUT_INV result$1 result$2))))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           (not or.cond$1_0)
                           (let
                              ((sub5$1_0 (- n$1_0 1))
                               (m$2_0 m$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((cmp$2_0 (> m$2_0 0))
                                  (cmp1$2_0 (= n$2_0 0)))
                                 (let
                                    ((or.cond$2_0 (and
                                                      cmp$2_0
                                                      cmp1$2_0)))
                                    (=>
                                       (not or.cond$2_0)
                                       (let
                                          ((cmp2$2_0 (= m$2_0 0)))
                                          (=>
                                             (not cmp2$2_0)
                                             (let
                                                ((sub5$2_0 (- n$2_0 1)))
                                                (and
                                                   (INV_REC_f^f_PRE m$1_0 sub5$1_0 m$2_0 sub5$2_0)
                                                   (forall
                                                      ((call6$1_0 Int)
                                                       (call6$2_0 Int))
                                                      (=>
                                                         (INV_REC_f^f m$1_0 sub5$1_0 m$2_0 sub5$2_0 call6$1_0 call6$2_0)
                                                         (let
                                                            ((call6.sink$1_0 call6$1_0)
                                                             (sub7$1_0 (- m$1_0 1))
                                                             (sub7$2_0 (- m$2_0 1)))
                                                            (and
                                                               (INV_REC_f^f_PRE sub7$1_0 call6.sink$1_0 sub7$2_0 call6$2_0)
                                                               (forall
                                                                  ((call8$1_0 Int)
                                                                   (call8$2_0 Int))
                                                                  (=>
                                                                     (INV_REC_f^f sub7$1_0 call6.sink$1_0 sub7$2_0 call6$2_0 call8$1_0 call8$2_0)
                                                                     (let
                                                                        ((r.1$1_0 call8$1_0))
                                                                        (let
                                                                           ((result$1 r.1$1_0)
                                                                            (r.1$2_0 call8$2_0))
                                                                           (let
                                                                              ((result$2 r.1$2_0))
                                                                              (OUT_INV result$1 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((add$1_0 (+ n$1_0 1)))
                     (let
                        ((r.1$1_0 add$1_0))
                        (let
                           ((result$1 r.1$1_0)
                            (m$2_0 m$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((cmp$2_0 (> m$2_0 0))
                               (cmp1$2_0 (= n$2_0 0)))
                              (let
                                 ((or.cond$2_0 (and
                                                   cmp$2_0
                                                   cmp1$2_0)))
                                 (=>
                                    or.cond$2_0
                                    (let
                                       ((sub$2_0 (- m$2_0 1)))
                                       (and
                                          (INV_REC_f__2_PRE sub$2_0 1)
                                          (forall
                                             ((call$2_0 Int))
                                             (=>
                                                (INV_REC_f__2 sub$2_0 1 call$2_0)
                                                (let
                                                   ((r.1$2_0 call$2_0))
                                                   (let
                                                      ((result$2 r.1$2_0))
                                                      (INV_REC_f^f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((add$1_0 (+ n$1_0 1)))
                     (let
                        ((r.1$1_0 add$1_0))
                        (let
                           ((result$1 r.1$1_0)
                            (m$2_0 m$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((cmp$2_0 (> m$2_0 0))
                               (cmp1$2_0 (= n$2_0 0)))
                              (let
                                 ((or.cond$2_0 (and
                                                   cmp$2_0
                                                   cmp1$2_0)))
                                 (=>
                                    (not or.cond$2_0)
                                    (let
                                       ((cmp2$2_0 (= m$2_0 0)))
                                       (=>
                                          cmp2$2_0
                                          (let
                                             ((add$2_0 (+ n$2_0 1)))
                                             (let
                                                ((r.1$2_0 add$2_0))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (INV_REC_f^f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((add$1_0 (+ n$1_0 1)))
                     (let
                        ((r.1$1_0 add$1_0))
                        (let
                           ((result$1 r.1$1_0)
                            (m$2_0 m$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((cmp$2_0 (> m$2_0 0))
                               (cmp1$2_0 (= n$2_0 0)))
                              (let
                                 ((or.cond$2_0 (and
                                                   cmp$2_0
                                                   cmp1$2_0)))
                                 (=>
                                    (not or.cond$2_0)
                                    (let
                                       ((cmp2$2_0 (= m$2_0 0)))
                                       (=>
                                          (not cmp2$2_0)
                                          (let
                                             ((sub5$2_0 (- n$2_0 1)))
                                             (and
                                                (INV_REC_f__2_PRE m$2_0 sub5$2_0)
                                                (forall
                                                   ((call6$2_0 Int))
                                                   (=>
                                                      (INV_REC_f__2 m$2_0 sub5$2_0 call6$2_0)
                                                      (let
                                                         ((sub7$2_0 (- m$2_0 1)))
                                                         (and
                                                            (INV_REC_f__2_PRE sub7$2_0 call6$2_0)
                                                            (forall
                                                               ((call8$2_0 Int))
                                                               (=>
                                                                  (INV_REC_f__2 sub7$2_0 call6$2_0 call8$2_0)
                                                                  (let
                                                                     ((r.1$2_0 call8$2_0))
                                                                     (let
                                                                        ((result$2 r.1$2_0))
                                                                        (INV_REC_f^f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           or.cond$1_0
                           (let
                              ((call6.sink$1_0 1)
                               (sub7$1_0 (- m$1_0 1))
                               (m$2_0 m$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((cmp$2_0 (> m$2_0 0))
                                  (cmp1$2_0 (= n$2_0 0)))
                                 (let
                                    ((or.cond$2_0 (and
                                                      cmp$2_0
                                                      cmp1$2_0)))
                                    (=>
                                       or.cond$2_0
                                       (let
                                          ((sub$2_0 (- m$2_0 1)))
                                          (and
                                             (INV_REC_f^f_PRE sub7$1_0 call6.sink$1_0 sub$2_0 1)
                                             (forall
                                                ((call8$1_0 Int)
                                                 (call$2_0 Int))
                                                (=>
                                                   (INV_REC_f^f sub7$1_0 call6.sink$1_0 sub$2_0 1 call8$1_0 call$2_0)
                                                   (let
                                                      ((r.1$1_0 call8$1_0))
                                                      (let
                                                         ((result$1 r.1$1_0)
                                                          (r.1$2_0 call$2_0))
                                                         (let
                                                            ((result$2 r.1$2_0))
                                                            (INV_REC_f^f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           or.cond$1_0
                           (let
                              ((call6.sink$1_0 1)
                               (sub7$1_0 (- m$1_0 1))
                               (m$2_0 m$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((cmp$2_0 (> m$2_0 0))
                                  (cmp1$2_0 (= n$2_0 0)))
                                 (let
                                    ((or.cond$2_0 (and
                                                      cmp$2_0
                                                      cmp1$2_0)))
                                    (=>
                                       (not or.cond$2_0)
                                       (let
                                          ((cmp2$2_0 (= m$2_0 0)))
                                          (=>
                                             cmp2$2_0
                                             (let
                                                ((add$2_0 (+ n$2_0 1)))
                                                (let
                                                   ((r.1$2_0 add$2_0))
                                                   (let
                                                      ((result$2 r.1$2_0))
                                                      (and
                                                         (INV_REC_f__1_PRE sub7$1_0 call6.sink$1_0)
                                                         (forall
                                                            ((call8$1_0 Int))
                                                            (=>
                                                               (INV_REC_f__1 sub7$1_0 call6.sink$1_0 call8$1_0)
                                                               (let
                                                                  ((r.1$1_0 call8$1_0))
                                                                  (let
                                                                     ((result$1 r.1$1_0))
                                                                     (INV_REC_f^f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           or.cond$1_0
                           (let
                              ((call6.sink$1_0 1)
                               (sub7$1_0 (- m$1_0 1))
                               (m$2_0 m$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((cmp$2_0 (> m$2_0 0))
                                  (cmp1$2_0 (= n$2_0 0)))
                                 (let
                                    ((or.cond$2_0 (and
                                                      cmp$2_0
                                                      cmp1$2_0)))
                                    (=>
                                       (not or.cond$2_0)
                                       (let
                                          ((cmp2$2_0 (= m$2_0 0)))
                                          (=>
                                             (not cmp2$2_0)
                                             (let
                                                ((sub5$2_0 (- n$2_0 1)))
                                                (and
                                                   (INV_REC_f__2_PRE m$2_0 sub5$2_0)
                                                   (forall
                                                      ((call6$2_0 Int))
                                                      (=>
                                                         (INV_REC_f__2 m$2_0 sub5$2_0 call6$2_0)
                                                         (let
                                                            ((sub7$2_0 (- m$2_0 1)))
                                                            (and
                                                               (INV_REC_f^f_PRE sub7$1_0 call6.sink$1_0 sub7$2_0 call6$2_0)
                                                               (forall
                                                                  ((call8$1_0 Int)
                                                                   (call8$2_0 Int))
                                                                  (=>
                                                                     (INV_REC_f^f sub7$1_0 call6.sink$1_0 sub7$2_0 call6$2_0 call8$1_0 call8$2_0)
                                                                     (let
                                                                        ((r.1$1_0 call8$1_0))
                                                                        (let
                                                                           ((result$1 r.1$1_0)
                                                                            (r.1$2_0 call8$2_0))
                                                                           (let
                                                                              ((result$2 r.1$2_0))
                                                                              (INV_REC_f^f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           (not or.cond$1_0)
                           (let
                              ((sub5$1_0 (- n$1_0 1))
                               (m$2_0 m$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((cmp$2_0 (> m$2_0 0))
                                  (cmp1$2_0 (= n$2_0 0)))
                                 (let
                                    ((or.cond$2_0 (and
                                                      cmp$2_0
                                                      cmp1$2_0)))
                                    (=>
                                       or.cond$2_0
                                       (let
                                          ((sub$2_0 (- m$2_0 1)))
                                          (and
                                             (INV_REC_f__1_PRE m$1_0 sub5$1_0)
                                             (forall
                                                ((call6$1_0 Int))
                                                (=>
                                                   (INV_REC_f__1 m$1_0 sub5$1_0 call6$1_0)
                                                   (let
                                                      ((call6.sink$1_0 call6$1_0)
                                                       (sub7$1_0 (- m$1_0 1)))
                                                      (and
                                                         (INV_REC_f^f_PRE sub7$1_0 call6.sink$1_0 sub$2_0 1)
                                                         (forall
                                                            ((call8$1_0 Int)
                                                             (call$2_0 Int))
                                                            (=>
                                                               (INV_REC_f^f sub7$1_0 call6.sink$1_0 sub$2_0 1 call8$1_0 call$2_0)
                                                               (let
                                                                  ((r.1$1_0 call8$1_0))
                                                                  (let
                                                                     ((result$1 r.1$1_0)
                                                                      (r.1$2_0 call$2_0))
                                                                     (let
                                                                        ((result$2 r.1$2_0))
                                                                        (INV_REC_f^f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           (not or.cond$1_0)
                           (let
                              ((sub5$1_0 (- n$1_0 1))
                               (m$2_0 m$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((cmp$2_0 (> m$2_0 0))
                                  (cmp1$2_0 (= n$2_0 0)))
                                 (let
                                    ((or.cond$2_0 (and
                                                      cmp$2_0
                                                      cmp1$2_0)))
                                    (=>
                                       (not or.cond$2_0)
                                       (let
                                          ((cmp2$2_0 (= m$2_0 0)))
                                          (=>
                                             cmp2$2_0
                                             (let
                                                ((add$2_0 (+ n$2_0 1)))
                                                (let
                                                   ((r.1$2_0 add$2_0))
                                                   (let
                                                      ((result$2 r.1$2_0))
                                                      (and
                                                         (INV_REC_f__1_PRE m$1_0 sub5$1_0)
                                                         (forall
                                                            ((call6$1_0 Int))
                                                            (=>
                                                               (INV_REC_f__1 m$1_0 sub5$1_0 call6$1_0)
                                                               (let
                                                                  ((call6.sink$1_0 call6$1_0)
                                                                   (sub7$1_0 (- m$1_0 1)))
                                                                  (and
                                                                     (INV_REC_f__1_PRE sub7$1_0 call6.sink$1_0)
                                                                     (forall
                                                                        ((call8$1_0 Int))
                                                                        (=>
                                                                           (INV_REC_f__1 sub7$1_0 call6.sink$1_0 call8$1_0)
                                                                           (let
                                                                              ((r.1$1_0 call8$1_0))
                                                                              (let
                                                                                 ((result$1 r.1$1_0))
                                                                                 (INV_REC_f^f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f^f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           (not or.cond$1_0)
                           (let
                              ((sub5$1_0 (- n$1_0 1))
                               (m$2_0 m$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((cmp$2_0 (> m$2_0 0))
                                  (cmp1$2_0 (= n$2_0 0)))
                                 (let
                                    ((or.cond$2_0 (and
                                                      cmp$2_0
                                                      cmp1$2_0)))
                                    (=>
                                       (not or.cond$2_0)
                                       (let
                                          ((cmp2$2_0 (= m$2_0 0)))
                                          (=>
                                             (not cmp2$2_0)
                                             (let
                                                ((sub5$2_0 (- n$2_0 1)))
                                                (and
                                                   (INV_REC_f^f_PRE m$1_0 sub5$1_0 m$2_0 sub5$2_0)
                                                   (forall
                                                      ((call6$1_0 Int)
                                                       (call6$2_0 Int))
                                                      (=>
                                                         (INV_REC_f^f m$1_0 sub5$1_0 m$2_0 sub5$2_0 call6$1_0 call6$2_0)
                                                         (let
                                                            ((call6.sink$1_0 call6$1_0)
                                                             (sub7$1_0 (- m$1_0 1))
                                                             (sub7$2_0 (- m$2_0 1)))
                                                            (and
                                                               (INV_REC_f^f_PRE sub7$1_0 call6.sink$1_0 sub7$2_0 call6$2_0)
                                                               (forall
                                                                  ((call8$1_0 Int)
                                                                   (call8$2_0 Int))
                                                                  (=>
                                                                     (INV_REC_f^f sub7$1_0 call6.sink$1_0 sub7$2_0 call6$2_0 call8$1_0 call8$2_0)
                                                                     (let
                                                                        ((r.1$1_0 call8$1_0))
                                                                        (let
                                                                           ((result$1 r.1$1_0)
                                                                            (r.1$2_0 call8$2_0))
                                                                           (let
                                                                              ((result$2 r.1$2_0))
                                                                              (INV_REC_f^f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE m$1_0_old n$1_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((add$1_0 (+ n$1_0 1)))
                     (let
                        ((r.1$1_0 add$1_0))
                        (let
                           ((result$1 r.1$1_0))
                           (INV_REC_f__1 m$1_0_old n$1_0_old result$1))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE m$1_0_old n$1_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           or.cond$1_0
                           (let
                              ((call6.sink$1_0 1)
                               (sub7$1_0 (- m$1_0 1)))
                              (and
                                 (INV_REC_f__1_PRE sub7$1_0 call6.sink$1_0)
                                 (forall
                                    ((call8$1_0 Int))
                                    (=>
                                       (INV_REC_f__1 sub7$1_0 call6.sink$1_0 call8$1_0)
                                       (let
                                          ((r.1$1_0 call8$1_0))
                                          (let
                                             ((result$1 r.1$1_0))
                                             (INV_REC_f__1 m$1_0_old n$1_0_old result$1))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE m$1_0_old n$1_0_old)
         (let
            ((m$1_0 m$1_0_old))
            (let
               ((n$1_0 n$1_0_old)
                (cmp$1_0 (= m$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((cmp1$1_0 (> m$1_0 0))
                      (cmp2$1_0 (= n$1_0 0)))
                     (let
                        ((or.cond$1_0 (and
                                          cmp1$1_0
                                          cmp2$1_0)))
                        (=>
                           (not or.cond$1_0)
                           (let
                              ((sub5$1_0 (- n$1_0 1)))
                              (and
                                 (INV_REC_f__1_PRE m$1_0 sub5$1_0)
                                 (forall
                                    ((call6$1_0 Int))
                                    (=>
                                       (INV_REC_f__1 m$1_0 sub5$1_0 call6$1_0)
                                       (let
                                          ((call6.sink$1_0 call6$1_0)
                                           (sub7$1_0 (- m$1_0 1)))
                                          (and
                                             (INV_REC_f__1_PRE sub7$1_0 call6.sink$1_0)
                                             (forall
                                                ((call8$1_0 Int))
                                                (=>
                                                   (INV_REC_f__1 sub7$1_0 call6.sink$1_0 call8$1_0)
                                                   (let
                                                      ((r.1$1_0 call8$1_0))
                                                      (let
                                                         ((result$1 r.1$1_0))
                                                         (INV_REC_f__1 m$1_0_old n$1_0_old result$1))))))))))))))))))))
(assert
   (forall
      ((m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE m$2_0_old n$2_0_old)
         (let
            ((m$2_0 m$2_0_old)
             (n$2_0 n$2_0_old))
            (let
               ((cmp$2_0 (> m$2_0 0))
                (cmp1$2_0 (= n$2_0 0)))
               (let
                  ((or.cond$2_0 (and
                                    cmp$2_0
                                    cmp1$2_0)))
                  (=>
                     or.cond$2_0
                     (let
                        ((sub$2_0 (- m$2_0 1)))
                        (and
                           (INV_REC_f__2_PRE sub$2_0 1)
                           (forall
                              ((call$2_0 Int))
                              (=>
                                 (INV_REC_f__2 sub$2_0 1 call$2_0)
                                 (let
                                    ((r.1$2_0 call$2_0))
                                    (let
                                       ((result$2 r.1$2_0))
                                       (INV_REC_f__2 m$2_0_old n$2_0_old result$2))))))))))))))
(assert
   (forall
      ((m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE m$2_0_old n$2_0_old)
         (let
            ((m$2_0 m$2_0_old)
             (n$2_0 n$2_0_old))
            (let
               ((cmp$2_0 (> m$2_0 0))
                (cmp1$2_0 (= n$2_0 0)))
               (let
                  ((or.cond$2_0 (and
                                    cmp$2_0
                                    cmp1$2_0)))
                  (=>
                     (not or.cond$2_0)
                     (let
                        ((cmp2$2_0 (= m$2_0 0)))
                        (=>
                           cmp2$2_0
                           (let
                              ((add$2_0 (+ n$2_0 1)))
                              (let
                                 ((r.1$2_0 add$2_0))
                                 (let
                                    ((result$2 r.1$2_0))
                                    (INV_REC_f__2 m$2_0_old n$2_0_old result$2)))))))))))))
(assert
   (forall
      ((m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE m$2_0_old n$2_0_old)
         (let
            ((m$2_0 m$2_0_old)
             (n$2_0 n$2_0_old))
            (let
               ((cmp$2_0 (> m$2_0 0))
                (cmp1$2_0 (= n$2_0 0)))
               (let
                  ((or.cond$2_0 (and
                                    cmp$2_0
                                    cmp1$2_0)))
                  (=>
                     (not or.cond$2_0)
                     (let
                        ((cmp2$2_0 (= m$2_0 0)))
                        (=>
                           (not cmp2$2_0)
                           (let
                              ((sub5$2_0 (- n$2_0 1)))
                              (and
                                 (INV_REC_f__2_PRE m$2_0 sub5$2_0)
                                 (forall
                                    ((call6$2_0 Int))
                                    (=>
                                       (INV_REC_f__2 m$2_0 sub5$2_0 call6$2_0)
                                       (let
                                          ((sub7$2_0 (- m$2_0 1)))
                                          (and
                                             (INV_REC_f__2_PRE sub7$2_0 call6$2_0)
                                             (forall
                                                ((call8$2_0 Int))
                                                (=>
                                                   (INV_REC_f__2 sub7$2_0 call6$2_0 call8$2_0)
                                                   (let
                                                      ((r.1$2_0 call8$2_0))
                                                      (let
                                                         ((result$2 r.1$2_0))
                                                         (INV_REC_f__2 m$2_0_old n$2_0_old result$2))))))))))))))))))))
(check-sat)
(get-model)
