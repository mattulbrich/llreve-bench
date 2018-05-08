;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((x$1_0 Int)
    (g$1_0 Int)
    (x$2_0 Int)
    (g$2_0 Int))
   Bool
   (and
      (= x$1_0 x$2_0)
      (= g$1_0 g$2_0)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
; :annot (INV_MAIN_23 add$1_0 g.addr.1.sink$1_0 x.addr.1$1_0 add$2_0 g.addr.1$2_0 x.addr.1$2_0)
(declare-fun
   INV_MAIN_23
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
; :annot (INV_MAIN_42 g.addr.0$1_0 i.0$1_0 x.addr.0$1_0 g.addr.0$2_0 i.0$2_0 x.addr.0$2_0)
(declare-fun
   INV_MAIN_42
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((x$1_0_old Int)
       (g$1_0_old Int)
       (x$2_0_old Int)
       (g$2_0_old Int))
      (=>
         (IN_INV x$1_0_old g$1_0_old x$2_0_old g$2_0_old)
         (let
            ((x$1_0 x$1_0_old)
             (g$1_0 g$1_0_old))
            (let
               ((i.0$1_0 0)
                (g.addr.0$1_0 g$1_0)
                (x.addr.0$1_0 x$1_0)
                (x$2_0 x$2_0_old)
                (g$2_0 g$2_0_old))
               (let
                  ((i.0$2_0 0)
                   (g.addr.0$2_0 g$2_0)
                   (x.addr.0$2_0 x$2_0))
                  (INV_MAIN_42 g.addr.0$1_0 i.0$1_0 x.addr.0$1_0 g.addr.0$2_0 i.0$2_0 x.addr.0$2_0)))))))
(assert
   (forall
      ((add$1_0_old Int)
       (g.addr.1.sink$1_0_old Int)
       (x.addr.1$1_0_old Int)
       (add$2_0_old Int)
       (g.addr.1$2_0_old Int)
       (x.addr.1$2_0_old Int))
      (=>
         (INV_MAIN_23 add$1_0_old g.addr.1.sink$1_0_old x.addr.1$1_0_old add$2_0_old g.addr.1$2_0_old x.addr.1$2_0_old)
         (let
            ((add$1_0 add$1_0_old)
             (g.addr.1.sink$1_0 g.addr.1.sink$1_0_old)
             (x.addr.1$1_0 x.addr.1$1_0_old))
            (let
               ((add11$1_0 (+ g.addr.1.sink$1_0 1))
                (cmp4$1_0 (< x.addr.1$1_0 add$1_0)))
               (=>
                  cmp4$1_0
                  (let
                     ((add9$1_0 (+ x.addr.1$1_0 2)))
                     (let
                        ((sub10$1_0 (- add9$1_0 1)))
                        (let
                           ((g.addr.1.sink$1_0 add11$1_0)
                            (x.addr.1$1_0 sub10$1_0)
                            (add$2_0 add$2_0_old)
                            (g.addr.1$2_0 g.addr.1$2_0_old)
                            (x.addr.1$2_0 x.addr.1$2_0_old))
                           (let
                              ((cmp3$2_0 (< x.addr.1$2_0 add$2_0)))
                              (=>
                                 cmp3$2_0
                                 (let
                                    ((add8$2_0 (+ x.addr.1$2_0 1))
                                     (add9$2_0 (+ g.addr.1$2_0 2)))
                                    (let
                                       ((g.addr.1$2_0 add9$2_0)
                                        (x.addr.1$2_0 add8$2_0))
                                       (INV_MAIN_23 add$1_0 g.addr.1.sink$1_0 x.addr.1$1_0 add$2_0 g.addr.1$2_0 x.addr.1$2_0))))))))))))))
(assert
   (forall
      ((add$1_0_old Int)
       (g.addr.1.sink$1_0_old Int)
       (x.addr.1$1_0_old Int)
       (add$2_0_old Int)
       (g.addr.1$2_0_old Int)
       (x.addr.1$2_0_old Int))
      (=>
         (INV_MAIN_23 add$1_0_old g.addr.1.sink$1_0_old x.addr.1$1_0_old add$2_0_old g.addr.1$2_0_old x.addr.1$2_0_old)
         (let
            ((add$1_0 add$1_0_old)
             (g.addr.1.sink$1_0 g.addr.1.sink$1_0_old)
             (x.addr.1$1_0 x.addr.1$1_0_old))
            (let
               ((add11$1_0 (+ g.addr.1.sink$1_0 1))
                (cmp4$1_0 (< x.addr.1$1_0 add$1_0)))
               (=>
                  cmp4$1_0
                  (let
                     ((add9$1_0 (+ x.addr.1$1_0 2)))
                     (let
                        ((sub10$1_0 (- add9$1_0 1)))
                        (let
                           ((g.addr.1.sink$1_0 add11$1_0)
                            (x.addr.1$1_0 sub10$1_0))
                           (=>
                              (let
                                 ((add$2_0 add$2_0_old)
                                  (g.addr.1$2_0 g.addr.1$2_0_old)
                                  (x.addr.1$2_0 x.addr.1$2_0_old))
                                 (let
                                    ((cmp3$2_0 (< x.addr.1$2_0 add$2_0)))
                                    (=>
                                       cmp3$2_0
                                       (let
                                          ((add8$2_0 (+ x.addr.1$2_0 1))
                                           (add9$2_0 (+ g.addr.1$2_0 2)))
                                          (let
                                             ((g.addr.1$2_0 add9$2_0)
                                              (x.addr.1$2_0 add8$2_0))
                                             false)))))
                              (INV_MAIN_23 add$1_0 g.addr.1.sink$1_0 x.addr.1$1_0 add$2_0_old g.addr.1$2_0_old x.addr.1$2_0_old)))))))))))
(assert
   (forall
      ((add$1_0_old Int)
       (g.addr.1.sink$1_0_old Int)
       (x.addr.1$1_0_old Int)
       (add$2_0_old Int)
       (g.addr.1$2_0_old Int)
       (x.addr.1$2_0_old Int))
      (=>
         (INV_MAIN_23 add$1_0_old g.addr.1.sink$1_0_old x.addr.1$1_0_old add$2_0_old g.addr.1$2_0_old x.addr.1$2_0_old)
         (let
            ((add$2_0 add$2_0_old)
             (g.addr.1$2_0 g.addr.1$2_0_old)
             (x.addr.1$2_0 x.addr.1$2_0_old))
            (let
               ((cmp3$2_0 (< x.addr.1$2_0 add$2_0)))
               (=>
                  cmp3$2_0
                  (let
                     ((add8$2_0 (+ x.addr.1$2_0 1))
                      (add9$2_0 (+ g.addr.1$2_0 2)))
                     (let
                        ((g.addr.1$2_0 add9$2_0)
                         (x.addr.1$2_0 add8$2_0))
                        (=>
                           (let
                              ((add$1_0 add$1_0_old)
                               (g.addr.1.sink$1_0 g.addr.1.sink$1_0_old)
                               (x.addr.1$1_0 x.addr.1$1_0_old))
                              (let
                                 ((add11$1_0 (+ g.addr.1.sink$1_0 1))
                                  (cmp4$1_0 (< x.addr.1$1_0 add$1_0)))
                                 (=>
                                    cmp4$1_0
                                    (let
                                       ((add9$1_0 (+ x.addr.1$1_0 2)))
                                       (let
                                          ((sub10$1_0 (- add9$1_0 1)))
                                          (let
                                             ((g.addr.1.sink$1_0 add11$1_0)
                                              (x.addr.1$1_0 sub10$1_0))
                                             false))))))
                           (INV_MAIN_23 add$1_0_old g.addr.1.sink$1_0_old x.addr.1$1_0_old add$2_0 g.addr.1$2_0 x.addr.1$2_0))))))))))
(assert
   (forall
      ((add$1_0_old Int)
       (g.addr.1.sink$1_0_old Int)
       (x.addr.1$1_0_old Int)
       (add$2_0_old Int)
       (g.addr.1$2_0_old Int)
       (x.addr.1$2_0_old Int))
      (=>
         (INV_MAIN_23 add$1_0_old g.addr.1.sink$1_0_old x.addr.1$1_0_old add$2_0_old g.addr.1$2_0_old x.addr.1$2_0_old)
         (let
            ((add$1_0 add$1_0_old)
             (g.addr.1.sink$1_0 g.addr.1.sink$1_0_old)
             (x.addr.1$1_0 x.addr.1$1_0_old))
            (let
               ((add11$1_0 (+ g.addr.1.sink$1_0 1))
                (cmp4$1_0 (< x.addr.1$1_0 add$1_0)))
               (=>
                  (not cmp4$1_0)
                  (let
                     ((i.0$1_0 add$1_0)
                      (g.addr.0$1_0 add11$1_0)
                      (x.addr.0$1_0 x.addr.1$1_0)
                      (add$2_0 add$2_0_old)
                      (g.addr.1$2_0 g.addr.1$2_0_old)
                      (x.addr.1$2_0 x.addr.1$2_0_old))
                     (let
                        ((cmp3$2_0 (< x.addr.1$2_0 add$2_0)))
                        (=>
                           (not cmp3$2_0)
                           (let
                              ((i.0$2_0 add$2_0)
                               (g.addr.0$2_0 g.addr.1$2_0)
                               (x.addr.0$2_0 x.addr.1$2_0))
                              (INV_MAIN_42 g.addr.0$1_0 i.0$1_0 x.addr.0$1_0 g.addr.0$2_0 i.0$2_0 x.addr.0$2_0)))))))))))
(assert
   (forall
      ((g.addr.0$1_0_old Int)
       (i.0$1_0_old Int)
       (x.addr.0$1_0_old Int)
       (g.addr.0$2_0_old Int)
       (i.0$2_0_old Int)
       (x.addr.0$2_0_old Int))
      (=>
         (INV_MAIN_42 g.addr.0$1_0_old i.0$1_0_old x.addr.0$1_0_old g.addr.0$2_0_old i.0$2_0_old x.addr.0$2_0_old)
         (let
            ((g.addr.0$1_0 g.addr.0$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (x.addr.0$1_0 x.addr.0$1_0_old))
            (let
               ((cmp$1_0 (< i.0$1_0 x.addr.0$1_0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 g.addr.0$1_0)
                      (g.addr.0$2_0 g.addr.0$2_0_old)
                      (i.0$2_0 i.0$2_0_old)
                      (x.addr.0$2_0 x.addr.0$2_0_old))
                     (let
                        ((cmp$2_0 (< i.0$2_0 x.addr.0$2_0)))
                        (=>
                           cmp$2_0
                           (let
                              ((add$2_0 (+ i.0$2_0 1))
                               (sub$2_0 (- g.addr.0$2_0 2)))
                              (let
                                 ((g.addr.1$2_0 sub$2_0)
                                  (x.addr.1$2_0 x.addr.0$2_0))
                                 false)))))))))))
(assert
   (forall
      ((g.addr.0$1_0_old Int)
       (i.0$1_0_old Int)
       (x.addr.0$1_0_old Int)
       (g.addr.0$2_0_old Int)
       (i.0$2_0_old Int)
       (x.addr.0$2_0_old Int))
      (=>
         (INV_MAIN_42 g.addr.0$1_0_old i.0$1_0_old x.addr.0$1_0_old g.addr.0$2_0_old i.0$2_0_old x.addr.0$2_0_old)
         (let
            ((g.addr.0$1_0 g.addr.0$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (x.addr.0$1_0 x.addr.0$1_0_old))
            (let
               ((cmp$1_0 (< i.0$1_0 x.addr.0$1_0)))
               (=>
                  cmp$1_0
                  (let
                     ((add$1_0 (+ i.0$1_0 1))
                      (sub$1_0 (- g.addr.0$1_0 2)))
                     (let
                        ((g.addr.1.sink$1_0 sub$1_0)
                         (x.addr.1$1_0 x.addr.0$1_0)
                         (g.addr.0$2_0 g.addr.0$2_0_old)
                         (i.0$2_0 i.0$2_0_old)
                         (x.addr.0$2_0 x.addr.0$2_0_old))
                        (let
                           ((cmp$2_0 (< i.0$2_0 x.addr.0$2_0)))
                           (=>
                              (not cmp$2_0)
                              (let
                                 ((result$2 g.addr.0$2_0))
                                 false)))))))))))
(assert
   (forall
      ((g.addr.0$1_0_old Int)
       (i.0$1_0_old Int)
       (x.addr.0$1_0_old Int)
       (g.addr.0$2_0_old Int)
       (i.0$2_0_old Int)
       (x.addr.0$2_0_old Int))
      (=>
         (INV_MAIN_42 g.addr.0$1_0_old i.0$1_0_old x.addr.0$1_0_old g.addr.0$2_0_old i.0$2_0_old x.addr.0$2_0_old)
         (let
            ((g.addr.0$1_0 g.addr.0$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (x.addr.0$1_0 x.addr.0$1_0_old))
            (let
               ((cmp$1_0 (< i.0$1_0 x.addr.0$1_0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 g.addr.0$1_0)
                      (g.addr.0$2_0 g.addr.0$2_0_old)
                      (i.0$2_0 i.0$2_0_old)
                      (x.addr.0$2_0 x.addr.0$2_0_old))
                     (let
                        ((cmp$2_0 (< i.0$2_0 x.addr.0$2_0)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((result$2 g.addr.0$2_0))
                              (OUT_INV result$1 result$2)))))))))))
(assert
   (forall
      ((g.addr.0$1_0_old Int)
       (i.0$1_0_old Int)
       (x.addr.0$1_0_old Int)
       (g.addr.0$2_0_old Int)
       (i.0$2_0_old Int)
       (x.addr.0$2_0_old Int))
      (=>
         (INV_MAIN_42 g.addr.0$1_0_old i.0$1_0_old x.addr.0$1_0_old g.addr.0$2_0_old i.0$2_0_old x.addr.0$2_0_old)
         (let
            ((g.addr.0$1_0 g.addr.0$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (x.addr.0$1_0 x.addr.0$1_0_old))
            (let
               ((cmp$1_0 (< i.0$1_0 x.addr.0$1_0)))
               (=>
                  cmp$1_0
                  (let
                     ((add$1_0 (+ i.0$1_0 1))
                      (sub$1_0 (- g.addr.0$1_0 2)))
                     (let
                        ((g.addr.1.sink$1_0 sub$1_0)
                         (x.addr.1$1_0 x.addr.0$1_0)
                         (g.addr.0$2_0 g.addr.0$2_0_old)
                         (i.0$2_0 i.0$2_0_old)
                         (x.addr.0$2_0 x.addr.0$2_0_old))
                        (let
                           ((cmp$2_0 (< i.0$2_0 x.addr.0$2_0)))
                           (=>
                              cmp$2_0
                              (let
                                 ((add$2_0 (+ i.0$2_0 1))
                                  (sub$2_0 (- g.addr.0$2_0 2)))
                                 (let
                                    ((g.addr.1$2_0 sub$2_0)
                                     (x.addr.1$2_0 x.addr.0$2_0))
                                    (INV_MAIN_23 add$1_0 g.addr.1.sink$1_0 x.addr.1$1_0 add$2_0 g.addr.1$2_0 x.addr.1$2_0)))))))))))))
(check-sat)
(get-model)
