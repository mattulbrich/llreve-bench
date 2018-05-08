;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((n$1_0 Int)
    (n$2_0 Int))
   Bool
   (= n$1_0 n$2_0))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
; :annot (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)
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
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV n$1_0_old n$2_0_old)
         (let
            ((n$1_0 n$1_0_old))
            (let
               ((div$1_0 (div n$1_0 10)))
               (let
                  ((result.0$1_0 1)
                   (n.addr.0$1_0 div$1_0)
                   (n$2_0 n$2_0_old))
                  (let
                     ((retval1.0$2_0 (- 1))
                      (b.0$2_0 1)
                      (result.0$2_0 1)
                      (n.addr.0$2_0 n$2_0))
                     (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 result.0$1_0)
                      (b.0$2_0 b.0$2_0_old))
                     (let
                        ((n.addr.0$2_0 n.addr.0$2_0_old)
                         (result.0$2_0 result.0$2_0_old)
                         (retval1.0$2_0 retval1.0$2_0_old)
                         (cmp$2_0 (= b.0$2_0 0)))
                        (let
                           ((lnot$2_0 (xor
                                          cmp$2_0
                                          true)))
                           (=>
                              (not lnot$2_0)
                              (let
                                 ((result$2 retval1.0$2_0))
                                 (OUT_INV result$1 result$2))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    cmp6$1_0
                                    (let
                                       ((inc9$1_0 (+ inc4$1_0 1))
                                        (div10$1_0 (div div5$1_0 10)))
                                       (let
                                          ((cmp11$1_0 (> div10$1_0 0)))
                                          (=>
                                             cmp11$1_0
                                             (let
                                                ((inc14$1_0 (+ inc9$1_0 1))
                                                 (div15$1_0 (div div10$1_0 10)))
                                                (let
                                                   ((result.0$1_0 inc14$1_0)
                                                    (n.addr.0$1_0 div15$1_0)
                                                    (b.0$2_0 b.0$2_0_old))
                                                   (let
                                                      ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                       (result.0$2_0 result.0$2_0_old)
                                                       (retval1.0$2_0 retval1.0$2_0_old)
                                                       (cmp$2_0 (= b.0$2_0 0)))
                                                      (let
                                                         ((lnot$2_0 (xor
                                                                        cmp$2_0
                                                                        true)))
                                                         (=>
                                                            lnot$2_0
                                                            (let
                                                               ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                               (=>
                                                                  cmp2$2_0
                                                                  (let
                                                                     ((retval1.0$2_0 result.0$2_0)
                                                                      (b.0$2_0 0)
                                                                      (result.0$2_0 result.0$2_0)
                                                                      (n.addr.0$2_0 n.addr.0$2_0))
                                                                     (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    cmp6$1_0
                                    (let
                                       ((inc9$1_0 (+ inc4$1_0 1))
                                        (div10$1_0 (div div5$1_0 10)))
                                       (let
                                          ((cmp11$1_0 (> div10$1_0 0)))
                                          (=>
                                             cmp11$1_0
                                             (let
                                                ((inc14$1_0 (+ inc9$1_0 1))
                                                 (div15$1_0 (div div10$1_0 10)))
                                                (let
                                                   ((result.0$1_0 inc14$1_0)
                                                    (n.addr.0$1_0 div15$1_0)
                                                    (b.0$2_0 b.0$2_0_old))
                                                   (let
                                                      ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                       (result.0$2_0 result.0$2_0_old)
                                                       (retval1.0$2_0 retval1.0$2_0_old)
                                                       (cmp$2_0 (= b.0$2_0 0)))
                                                      (let
                                                         ((lnot$2_0 (xor
                                                                        cmp$2_0
                                                                        true)))
                                                         (=>
                                                            lnot$2_0
                                                            (let
                                                               ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                               (=>
                                                                  (not cmp2$2_0)
                                                                  (let
                                                                     ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                     (=>
                                                                        cmp3$2_0
                                                                        (let
                                                                           ((add$2_0 (+ result.0$2_0 1)))
                                                                           (let
                                                                              ((retval1.0$2_0 add$2_0)
                                                                               (b.0$2_0 0)
                                                                               (result.0$2_0 result.0$2_0)
                                                                               (n.addr.0$2_0 n.addr.0$2_0))
                                                                              (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    cmp6$1_0
                                    (let
                                       ((inc9$1_0 (+ inc4$1_0 1))
                                        (div10$1_0 (div div5$1_0 10)))
                                       (let
                                          ((cmp11$1_0 (> div10$1_0 0)))
                                          (=>
                                             cmp11$1_0
                                             (let
                                                ((inc14$1_0 (+ inc9$1_0 1))
                                                 (div15$1_0 (div div10$1_0 10)))
                                                (let
                                                   ((result.0$1_0 inc14$1_0)
                                                    (n.addr.0$1_0 div15$1_0)
                                                    (b.0$2_0 b.0$2_0_old))
                                                   (let
                                                      ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                       (result.0$2_0 result.0$2_0_old)
                                                       (retval1.0$2_0 retval1.0$2_0_old)
                                                       (cmp$2_0 (= b.0$2_0 0)))
                                                      (let
                                                         ((lnot$2_0 (xor
                                                                        cmp$2_0
                                                                        true)))
                                                         (=>
                                                            lnot$2_0
                                                            (let
                                                               ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                               (=>
                                                                  (not cmp2$2_0)
                                                                  (let
                                                                     ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                     (=>
                                                                        (not cmp3$2_0)
                                                                        (let
                                                                           ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                           (=>
                                                                              cmp6$2_0
                                                                              (let
                                                                                 ((add8$2_0 (+ result.0$2_0 2)))
                                                                                 (let
                                                                                    ((retval1.0$2_0 add8$2_0)
                                                                                     (b.0$2_0 0)
                                                                                     (result.0$2_0 result.0$2_0)
                                                                                     (n.addr.0$2_0 n.addr.0$2_0))
                                                                                    (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    cmp6$1_0
                                    (let
                                       ((inc9$1_0 (+ inc4$1_0 1))
                                        (div10$1_0 (div div5$1_0 10)))
                                       (let
                                          ((cmp11$1_0 (> div10$1_0 0)))
                                          (=>
                                             cmp11$1_0
                                             (let
                                                ((inc14$1_0 (+ inc9$1_0 1))
                                                 (div15$1_0 (div div10$1_0 10)))
                                                (let
                                                   ((result.0$1_0 inc14$1_0)
                                                    (n.addr.0$1_0 div15$1_0)
                                                    (b.0$2_0 b.0$2_0_old))
                                                   (let
                                                      ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                       (result.0$2_0 result.0$2_0_old)
                                                       (retval1.0$2_0 retval1.0$2_0_old)
                                                       (cmp$2_0 (= b.0$2_0 0)))
                                                      (let
                                                         ((lnot$2_0 (xor
                                                                        cmp$2_0
                                                                        true)))
                                                         (=>
                                                            lnot$2_0
                                                            (let
                                                               ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                               (=>
                                                                  (not cmp2$2_0)
                                                                  (let
                                                                     ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                     (=>
                                                                        (not cmp3$2_0)
                                                                        (let
                                                                           ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                           (=>
                                                                              (not cmp6$2_0)
                                                                              (let
                                                                                 ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                                 (=>
                                                                                    cmp10$2_0
                                                                                    (let
                                                                                       ((add12$2_0 (+ result.0$2_0 3)))
                                                                                       (let
                                                                                          ((retval1.0$2_0 add12$2_0)
                                                                                           (b.0$2_0 0)
                                                                                           (result.0$2_0 result.0$2_0)
                                                                                           (n.addr.0$2_0 n.addr.0$2_0))
                                                                                          (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    cmp6$1_0
                                    (let
                                       ((inc9$1_0 (+ inc4$1_0 1))
                                        (div10$1_0 (div div5$1_0 10)))
                                       (let
                                          ((cmp11$1_0 (> div10$1_0 0)))
                                          (=>
                                             cmp11$1_0
                                             (let
                                                ((inc14$1_0 (+ inc9$1_0 1))
                                                 (div15$1_0 (div div10$1_0 10)))
                                                (let
                                                   ((result.0$1_0 inc14$1_0)
                                                    (n.addr.0$1_0 div15$1_0)
                                                    (b.0$2_0 b.0$2_0_old))
                                                   (let
                                                      ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                       (result.0$2_0 result.0$2_0_old)
                                                       (retval1.0$2_0 retval1.0$2_0_old)
                                                       (cmp$2_0 (= b.0$2_0 0)))
                                                      (let
                                                         ((lnot$2_0 (xor
                                                                        cmp$2_0
                                                                        true)))
                                                         (=>
                                                            lnot$2_0
                                                            (let
                                                               ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                               (=>
                                                                  (not cmp2$2_0)
                                                                  (let
                                                                     ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                     (=>
                                                                        (not cmp3$2_0)
                                                                        (let
                                                                           ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                           (=>
                                                                              (not cmp6$2_0)
                                                                              (let
                                                                                 ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                                 (=>
                                                                                    (not cmp10$2_0)
                                                                                    (let
                                                                                       ((div$2_0 (div n.addr.0$2_0 10000))
                                                                                        (add14$2_0 (+ result.0$2_0 4)))
                                                                                       (let
                                                                                          ((retval1.0$2_0 retval1.0$2_0)
                                                                                           (b.0$2_0 b.0$2_0)
                                                                                           (result.0$2_0 add14$2_0)
                                                                                           (n.addr.0$2_0 div$2_0))
                                                                                          (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    cmp6$1_0
                                    (let
                                       ((inc9$1_0 (+ inc4$1_0 1))
                                        (div10$1_0 (div div5$1_0 10)))
                                       (let
                                          ((cmp11$1_0 (> div10$1_0 0)))
                                          (=>
                                             (not cmp11$1_0)
                                             (let
                                                ((result.0$1_0 inc9$1_0)
                                                 (n.addr.0$1_0 div10$1_0)
                                                 (b.0$2_0 b.0$2_0_old))
                                                (let
                                                   ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                    (result.0$2_0 result.0$2_0_old)
                                                    (retval1.0$2_0 retval1.0$2_0_old)
                                                    (cmp$2_0 (= b.0$2_0 0)))
                                                   (let
                                                      ((lnot$2_0 (xor
                                                                     cmp$2_0
                                                                     true)))
                                                      (=>
                                                         lnot$2_0
                                                         (let
                                                            ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                            (=>
                                                               cmp2$2_0
                                                               (let
                                                                  ((retval1.0$2_0 result.0$2_0)
                                                                   (b.0$2_0 0)
                                                                   (result.0$2_0 result.0$2_0)
                                                                   (n.addr.0$2_0 n.addr.0$2_0))
                                                                  (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    cmp6$1_0
                                    (let
                                       ((inc9$1_0 (+ inc4$1_0 1))
                                        (div10$1_0 (div div5$1_0 10)))
                                       (let
                                          ((cmp11$1_0 (> div10$1_0 0)))
                                          (=>
                                             (not cmp11$1_0)
                                             (let
                                                ((result.0$1_0 inc9$1_0)
                                                 (n.addr.0$1_0 div10$1_0)
                                                 (b.0$2_0 b.0$2_0_old))
                                                (let
                                                   ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                    (result.0$2_0 result.0$2_0_old)
                                                    (retval1.0$2_0 retval1.0$2_0_old)
                                                    (cmp$2_0 (= b.0$2_0 0)))
                                                   (let
                                                      ((lnot$2_0 (xor
                                                                     cmp$2_0
                                                                     true)))
                                                      (=>
                                                         lnot$2_0
                                                         (let
                                                            ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                            (=>
                                                               (not cmp2$2_0)
                                                               (let
                                                                  ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                  (=>
                                                                     cmp3$2_0
                                                                     (let
                                                                        ((add$2_0 (+ result.0$2_0 1)))
                                                                        (let
                                                                           ((retval1.0$2_0 add$2_0)
                                                                            (b.0$2_0 0)
                                                                            (result.0$2_0 result.0$2_0)
                                                                            (n.addr.0$2_0 n.addr.0$2_0))
                                                                           (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0))))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    cmp6$1_0
                                    (let
                                       ((inc9$1_0 (+ inc4$1_0 1))
                                        (div10$1_0 (div div5$1_0 10)))
                                       (let
                                          ((cmp11$1_0 (> div10$1_0 0)))
                                          (=>
                                             (not cmp11$1_0)
                                             (let
                                                ((result.0$1_0 inc9$1_0)
                                                 (n.addr.0$1_0 div10$1_0)
                                                 (b.0$2_0 b.0$2_0_old))
                                                (let
                                                   ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                    (result.0$2_0 result.0$2_0_old)
                                                    (retval1.0$2_0 retval1.0$2_0_old)
                                                    (cmp$2_0 (= b.0$2_0 0)))
                                                   (let
                                                      ((lnot$2_0 (xor
                                                                     cmp$2_0
                                                                     true)))
                                                      (=>
                                                         lnot$2_0
                                                         (let
                                                            ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                            (=>
                                                               (not cmp2$2_0)
                                                               (let
                                                                  ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                  (=>
                                                                     (not cmp3$2_0)
                                                                     (let
                                                                        ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                        (=>
                                                                           cmp6$2_0
                                                                           (let
                                                                              ((add8$2_0 (+ result.0$2_0 2)))
                                                                              (let
                                                                                 ((retval1.0$2_0 add8$2_0)
                                                                                  (b.0$2_0 0)
                                                                                  (result.0$2_0 result.0$2_0)
                                                                                  (n.addr.0$2_0 n.addr.0$2_0))
                                                                                 (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0))))))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    cmp6$1_0
                                    (let
                                       ((inc9$1_0 (+ inc4$1_0 1))
                                        (div10$1_0 (div div5$1_0 10)))
                                       (let
                                          ((cmp11$1_0 (> div10$1_0 0)))
                                          (=>
                                             (not cmp11$1_0)
                                             (let
                                                ((result.0$1_0 inc9$1_0)
                                                 (n.addr.0$1_0 div10$1_0)
                                                 (b.0$2_0 b.0$2_0_old))
                                                (let
                                                   ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                    (result.0$2_0 result.0$2_0_old)
                                                    (retval1.0$2_0 retval1.0$2_0_old)
                                                    (cmp$2_0 (= b.0$2_0 0)))
                                                   (let
                                                      ((lnot$2_0 (xor
                                                                     cmp$2_0
                                                                     true)))
                                                      (=>
                                                         lnot$2_0
                                                         (let
                                                            ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                            (=>
                                                               (not cmp2$2_0)
                                                               (let
                                                                  ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                  (=>
                                                                     (not cmp3$2_0)
                                                                     (let
                                                                        ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                        (=>
                                                                           (not cmp6$2_0)
                                                                           (let
                                                                              ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                              (=>
                                                                                 cmp10$2_0
                                                                                 (let
                                                                                    ((add12$2_0 (+ result.0$2_0 3)))
                                                                                    (let
                                                                                       ((retval1.0$2_0 add12$2_0)
                                                                                        (b.0$2_0 0)
                                                                                        (result.0$2_0 result.0$2_0)
                                                                                        (n.addr.0$2_0 n.addr.0$2_0))
                                                                                       (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0))))))))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    cmp6$1_0
                                    (let
                                       ((inc9$1_0 (+ inc4$1_0 1))
                                        (div10$1_0 (div div5$1_0 10)))
                                       (let
                                          ((cmp11$1_0 (> div10$1_0 0)))
                                          (=>
                                             (not cmp11$1_0)
                                             (let
                                                ((result.0$1_0 inc9$1_0)
                                                 (n.addr.0$1_0 div10$1_0)
                                                 (b.0$2_0 b.0$2_0_old))
                                                (let
                                                   ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                    (result.0$2_0 result.0$2_0_old)
                                                    (retval1.0$2_0 retval1.0$2_0_old)
                                                    (cmp$2_0 (= b.0$2_0 0)))
                                                   (let
                                                      ((lnot$2_0 (xor
                                                                     cmp$2_0
                                                                     true)))
                                                      (=>
                                                         lnot$2_0
                                                         (let
                                                            ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                            (=>
                                                               (not cmp2$2_0)
                                                               (let
                                                                  ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                  (=>
                                                                     (not cmp3$2_0)
                                                                     (let
                                                                        ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                        (=>
                                                                           (not cmp6$2_0)
                                                                           (let
                                                                              ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                              (=>
                                                                                 (not cmp10$2_0)
                                                                                 (let
                                                                                    ((div$2_0 (div n.addr.0$2_0 10000))
                                                                                     (add14$2_0 (+ result.0$2_0 4)))
                                                                                    (let
                                                                                       ((retval1.0$2_0 retval1.0$2_0)
                                                                                        (b.0$2_0 b.0$2_0)
                                                                                        (result.0$2_0 add14$2_0)
                                                                                        (n.addr.0$2_0 div$2_0))
                                                                                       (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0))))))))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    (not cmp6$1_0)
                                    (let
                                       ((result.0$1_0 inc4$1_0)
                                        (n.addr.0$1_0 div5$1_0)
                                        (b.0$2_0 b.0$2_0_old))
                                       (let
                                          ((n.addr.0$2_0 n.addr.0$2_0_old)
                                           (result.0$2_0 result.0$2_0_old)
                                           (retval1.0$2_0 retval1.0$2_0_old)
                                           (cmp$2_0 (= b.0$2_0 0)))
                                          (let
                                             ((lnot$2_0 (xor
                                                            cmp$2_0
                                                            true)))
                                             (=>
                                                lnot$2_0
                                                (let
                                                   ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                   (=>
                                                      cmp2$2_0
                                                      (let
                                                         ((retval1.0$2_0 result.0$2_0)
                                                          (b.0$2_0 0)
                                                          (result.0$2_0 result.0$2_0)
                                                          (n.addr.0$2_0 n.addr.0$2_0))
                                                         (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    (not cmp6$1_0)
                                    (let
                                       ((result.0$1_0 inc4$1_0)
                                        (n.addr.0$1_0 div5$1_0)
                                        (b.0$2_0 b.0$2_0_old))
                                       (let
                                          ((n.addr.0$2_0 n.addr.0$2_0_old)
                                           (result.0$2_0 result.0$2_0_old)
                                           (retval1.0$2_0 retval1.0$2_0_old)
                                           (cmp$2_0 (= b.0$2_0 0)))
                                          (let
                                             ((lnot$2_0 (xor
                                                            cmp$2_0
                                                            true)))
                                             (=>
                                                lnot$2_0
                                                (let
                                                   ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                   (=>
                                                      (not cmp2$2_0)
                                                      (let
                                                         ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                         (=>
                                                            cmp3$2_0
                                                            (let
                                                               ((add$2_0 (+ result.0$2_0 1)))
                                                               (let
                                                                  ((retval1.0$2_0 add$2_0)
                                                                   (b.0$2_0 0)
                                                                   (result.0$2_0 result.0$2_0)
                                                                   (n.addr.0$2_0 n.addr.0$2_0))
                                                                  (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    (not cmp6$1_0)
                                    (let
                                       ((result.0$1_0 inc4$1_0)
                                        (n.addr.0$1_0 div5$1_0)
                                        (b.0$2_0 b.0$2_0_old))
                                       (let
                                          ((n.addr.0$2_0 n.addr.0$2_0_old)
                                           (result.0$2_0 result.0$2_0_old)
                                           (retval1.0$2_0 retval1.0$2_0_old)
                                           (cmp$2_0 (= b.0$2_0 0)))
                                          (let
                                             ((lnot$2_0 (xor
                                                            cmp$2_0
                                                            true)))
                                             (=>
                                                lnot$2_0
                                                (let
                                                   ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                   (=>
                                                      (not cmp2$2_0)
                                                      (let
                                                         ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                         (=>
                                                            (not cmp3$2_0)
                                                            (let
                                                               ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                               (=>
                                                                  cmp6$2_0
                                                                  (let
                                                                     ((add8$2_0 (+ result.0$2_0 2)))
                                                                     (let
                                                                        ((retval1.0$2_0 add8$2_0)
                                                                         (b.0$2_0 0)
                                                                         (result.0$2_0 result.0$2_0)
                                                                         (n.addr.0$2_0 n.addr.0$2_0))
                                                                        (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    (not cmp6$1_0)
                                    (let
                                       ((result.0$1_0 inc4$1_0)
                                        (n.addr.0$1_0 div5$1_0)
                                        (b.0$2_0 b.0$2_0_old))
                                       (let
                                          ((n.addr.0$2_0 n.addr.0$2_0_old)
                                           (result.0$2_0 result.0$2_0_old)
                                           (retval1.0$2_0 retval1.0$2_0_old)
                                           (cmp$2_0 (= b.0$2_0 0)))
                                          (let
                                             ((lnot$2_0 (xor
                                                            cmp$2_0
                                                            true)))
                                             (=>
                                                lnot$2_0
                                                (let
                                                   ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                   (=>
                                                      (not cmp2$2_0)
                                                      (let
                                                         ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                         (=>
                                                            (not cmp3$2_0)
                                                            (let
                                                               ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                               (=>
                                                                  (not cmp6$2_0)
                                                                  (let
                                                                     ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                     (=>
                                                                        cmp10$2_0
                                                                        (let
                                                                           ((add12$2_0 (+ result.0$2_0 3)))
                                                                           (let
                                                                              ((retval1.0$2_0 add12$2_0)
                                                                               (b.0$2_0 0)
                                                                               (result.0$2_0 result.0$2_0)
                                                                               (n.addr.0$2_0 n.addr.0$2_0))
                                                                              (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    (not cmp6$1_0)
                                    (let
                                       ((result.0$1_0 inc4$1_0)
                                        (n.addr.0$1_0 div5$1_0)
                                        (b.0$2_0 b.0$2_0_old))
                                       (let
                                          ((n.addr.0$2_0 n.addr.0$2_0_old)
                                           (result.0$2_0 result.0$2_0_old)
                                           (retval1.0$2_0 retval1.0$2_0_old)
                                           (cmp$2_0 (= b.0$2_0 0)))
                                          (let
                                             ((lnot$2_0 (xor
                                                            cmp$2_0
                                                            true)))
                                             (=>
                                                lnot$2_0
                                                (let
                                                   ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                   (=>
                                                      (not cmp2$2_0)
                                                      (let
                                                         ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                         (=>
                                                            (not cmp3$2_0)
                                                            (let
                                                               ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                               (=>
                                                                  (not cmp6$2_0)
                                                                  (let
                                                                     ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                     (=>
                                                                        (not cmp10$2_0)
                                                                        (let
                                                                           ((div$2_0 (div n.addr.0$2_0 10000))
                                                                            (add14$2_0 (+ result.0$2_0 4)))
                                                                           (let
                                                                              ((retval1.0$2_0 retval1.0$2_0)
                                                                               (b.0$2_0 b.0$2_0)
                                                                               (result.0$2_0 add14$2_0)
                                                                               (n.addr.0$2_0 div$2_0))
                                                                              (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((result.0$1_0 inc$1_0)
                               (n.addr.0$1_0 div1$1_0)
                               (b.0$2_0 b.0$2_0_old))
                              (let
                                 ((n.addr.0$2_0 n.addr.0$2_0_old)
                                  (result.0$2_0 result.0$2_0_old)
                                  (retval1.0$2_0 retval1.0$2_0_old)
                                  (cmp$2_0 (= b.0$2_0 0)))
                                 (let
                                    ((lnot$2_0 (xor
                                                   cmp$2_0
                                                   true)))
                                    (=>
                                       lnot$2_0
                                       (let
                                          ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                          (=>
                                             cmp2$2_0
                                             (let
                                                ((retval1.0$2_0 result.0$2_0)
                                                 (b.0$2_0 0)
                                                 (result.0$2_0 result.0$2_0)
                                                 (n.addr.0$2_0 n.addr.0$2_0))
                                                (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((result.0$1_0 inc$1_0)
                               (n.addr.0$1_0 div1$1_0)
                               (b.0$2_0 b.0$2_0_old))
                              (let
                                 ((n.addr.0$2_0 n.addr.0$2_0_old)
                                  (result.0$2_0 result.0$2_0_old)
                                  (retval1.0$2_0 retval1.0$2_0_old)
                                  (cmp$2_0 (= b.0$2_0 0)))
                                 (let
                                    ((lnot$2_0 (xor
                                                   cmp$2_0
                                                   true)))
                                    (=>
                                       lnot$2_0
                                       (let
                                          ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                          (=>
                                             (not cmp2$2_0)
                                             (let
                                                ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                (=>
                                                   cmp3$2_0
                                                   (let
                                                      ((add$2_0 (+ result.0$2_0 1)))
                                                      (let
                                                         ((retval1.0$2_0 add$2_0)
                                                          (b.0$2_0 0)
                                                          (result.0$2_0 result.0$2_0)
                                                          (n.addr.0$2_0 n.addr.0$2_0))
                                                         (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((result.0$1_0 inc$1_0)
                               (n.addr.0$1_0 div1$1_0)
                               (b.0$2_0 b.0$2_0_old))
                              (let
                                 ((n.addr.0$2_0 n.addr.0$2_0_old)
                                  (result.0$2_0 result.0$2_0_old)
                                  (retval1.0$2_0 retval1.0$2_0_old)
                                  (cmp$2_0 (= b.0$2_0 0)))
                                 (let
                                    ((lnot$2_0 (xor
                                                   cmp$2_0
                                                   true)))
                                    (=>
                                       lnot$2_0
                                       (let
                                          ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                          (=>
                                             (not cmp2$2_0)
                                             (let
                                                ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                (=>
                                                   (not cmp3$2_0)
                                                   (let
                                                      ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                      (=>
                                                         cmp6$2_0
                                                         (let
                                                            ((add8$2_0 (+ result.0$2_0 2)))
                                                            (let
                                                               ((retval1.0$2_0 add8$2_0)
                                                                (b.0$2_0 0)
                                                                (result.0$2_0 result.0$2_0)
                                                                (n.addr.0$2_0 n.addr.0$2_0))
                                                               (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((result.0$1_0 inc$1_0)
                               (n.addr.0$1_0 div1$1_0)
                               (b.0$2_0 b.0$2_0_old))
                              (let
                                 ((n.addr.0$2_0 n.addr.0$2_0_old)
                                  (result.0$2_0 result.0$2_0_old)
                                  (retval1.0$2_0 retval1.0$2_0_old)
                                  (cmp$2_0 (= b.0$2_0 0)))
                                 (let
                                    ((lnot$2_0 (xor
                                                   cmp$2_0
                                                   true)))
                                    (=>
                                       lnot$2_0
                                       (let
                                          ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                          (=>
                                             (not cmp2$2_0)
                                             (let
                                                ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                (=>
                                                   (not cmp3$2_0)
                                                   (let
                                                      ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                      (=>
                                                         (not cmp6$2_0)
                                                         (let
                                                            ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                            (=>
                                                               cmp10$2_0
                                                               (let
                                                                  ((add12$2_0 (+ result.0$2_0 3)))
                                                                  (let
                                                                     ((retval1.0$2_0 add12$2_0)
                                                                      (b.0$2_0 0)
                                                                      (result.0$2_0 result.0$2_0)
                                                                      (n.addr.0$2_0 n.addr.0$2_0))
                                                                     (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((result.0$1_0 inc$1_0)
                               (n.addr.0$1_0 div1$1_0)
                               (b.0$2_0 b.0$2_0_old))
                              (let
                                 ((n.addr.0$2_0 n.addr.0$2_0_old)
                                  (result.0$2_0 result.0$2_0_old)
                                  (retval1.0$2_0 retval1.0$2_0_old)
                                  (cmp$2_0 (= b.0$2_0 0)))
                                 (let
                                    ((lnot$2_0 (xor
                                                   cmp$2_0
                                                   true)))
                                    (=>
                                       lnot$2_0
                                       (let
                                          ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                          (=>
                                             (not cmp2$2_0)
                                             (let
                                                ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                (=>
                                                   (not cmp3$2_0)
                                                   (let
                                                      ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                      (=>
                                                         (not cmp6$2_0)
                                                         (let
                                                            ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                            (=>
                                                               (not cmp10$2_0)
                                                               (let
                                                                  ((div$2_0 (div n.addr.0$2_0 10000))
                                                                   (add14$2_0 (+ result.0$2_0 4)))
                                                                  (let
                                                                     ((retval1.0$2_0 retval1.0$2_0)
                                                                      (b.0$2_0 b.0$2_0)
                                                                      (result.0$2_0 add14$2_0)
                                                                      (n.addr.0$2_0 div$2_0))
                                                                     (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0))))))))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    cmp6$1_0
                                    (let
                                       ((inc9$1_0 (+ inc4$1_0 1))
                                        (div10$1_0 (div div5$1_0 10)))
                                       (let
                                          ((cmp11$1_0 (> div10$1_0 0)))
                                          (=>
                                             cmp11$1_0
                                             (let
                                                ((inc14$1_0 (+ inc9$1_0 1))
                                                 (div15$1_0 (div div10$1_0 10)))
                                                (let
                                                   ((result.0$1_0 inc14$1_0)
                                                    (n.addr.0$1_0 div15$1_0))
                                                   (=>
                                                      (and
                                                         (let
                                                            ((b.0$2_0 b.0$2_0_old))
                                                            (let
                                                               ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                                (result.0$2_0 result.0$2_0_old)
                                                                (retval1.0$2_0 retval1.0$2_0_old)
                                                                (cmp$2_0 (= b.0$2_0 0)))
                                                               (let
                                                                  ((lnot$2_0 (xor
                                                                                 cmp$2_0
                                                                                 true)))
                                                                  (=>
                                                                     lnot$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                                        (=>
                                                                           cmp2$2_0
                                                                           (let
                                                                              ((retval1.0$2_0 result.0$2_0)
                                                                               (b.0$2_0 0)
                                                                               (result.0$2_0 result.0$2_0)
                                                                               (n.addr.0$2_0 n.addr.0$2_0))
                                                                              false)))))))
                                                         (let
                                                            ((b.0$2_0 b.0$2_0_old))
                                                            (let
                                                               ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                                (result.0$2_0 result.0$2_0_old)
                                                                (retval1.0$2_0 retval1.0$2_0_old)
                                                                (cmp$2_0 (= b.0$2_0 0)))
                                                               (let
                                                                  ((lnot$2_0 (xor
                                                                                 cmp$2_0
                                                                                 true)))
                                                                  (=>
                                                                     lnot$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                                        (=>
                                                                           (not cmp2$2_0)
                                                                           (let
                                                                              ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                              (=>
                                                                                 cmp3$2_0
                                                                                 (let
                                                                                    ((add$2_0 (+ result.0$2_0 1)))
                                                                                    (let
                                                                                       ((retval1.0$2_0 add$2_0)
                                                                                        (b.0$2_0 0)
                                                                                        (result.0$2_0 result.0$2_0)
                                                                                        (n.addr.0$2_0 n.addr.0$2_0))
                                                                                       false))))))))))
                                                         (let
                                                            ((b.0$2_0 b.0$2_0_old))
                                                            (let
                                                               ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                                (result.0$2_0 result.0$2_0_old)
                                                                (retval1.0$2_0 retval1.0$2_0_old)
                                                                (cmp$2_0 (= b.0$2_0 0)))
                                                               (let
                                                                  ((lnot$2_0 (xor
                                                                                 cmp$2_0
                                                                                 true)))
                                                                  (=>
                                                                     lnot$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                                        (=>
                                                                           (not cmp2$2_0)
                                                                           (let
                                                                              ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                              (=>
                                                                                 (not cmp3$2_0)
                                                                                 (let
                                                                                    ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                                    (=>
                                                                                       cmp6$2_0
                                                                                       (let
                                                                                          ((add8$2_0 (+ result.0$2_0 2)))
                                                                                          (let
                                                                                             ((retval1.0$2_0 add8$2_0)
                                                                                              (b.0$2_0 0)
                                                                                              (result.0$2_0 result.0$2_0)
                                                                                              (n.addr.0$2_0 n.addr.0$2_0))
                                                                                             false))))))))))))
                                                         (let
                                                            ((b.0$2_0 b.0$2_0_old))
                                                            (let
                                                               ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                                (result.0$2_0 result.0$2_0_old)
                                                                (retval1.0$2_0 retval1.0$2_0_old)
                                                                (cmp$2_0 (= b.0$2_0 0)))
                                                               (let
                                                                  ((lnot$2_0 (xor
                                                                                 cmp$2_0
                                                                                 true)))
                                                                  (=>
                                                                     lnot$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                                        (=>
                                                                           (not cmp2$2_0)
                                                                           (let
                                                                              ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                              (=>
                                                                                 (not cmp3$2_0)
                                                                                 (let
                                                                                    ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                                    (=>
                                                                                       (not cmp6$2_0)
                                                                                       (let
                                                                                          ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                                          (=>
                                                                                             cmp10$2_0
                                                                                             (let
                                                                                                ((add12$2_0 (+ result.0$2_0 3)))
                                                                                                (let
                                                                                                   ((retval1.0$2_0 add12$2_0)
                                                                                                    (b.0$2_0 0)
                                                                                                    (result.0$2_0 result.0$2_0)
                                                                                                    (n.addr.0$2_0 n.addr.0$2_0))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((b.0$2_0 b.0$2_0_old))
                                                            (let
                                                               ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                                (result.0$2_0 result.0$2_0_old)
                                                                (retval1.0$2_0 retval1.0$2_0_old)
                                                                (cmp$2_0 (= b.0$2_0 0)))
                                                               (let
                                                                  ((lnot$2_0 (xor
                                                                                 cmp$2_0
                                                                                 true)))
                                                                  (=>
                                                                     lnot$2_0
                                                                     (let
                                                                        ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                                        (=>
                                                                           (not cmp2$2_0)
                                                                           (let
                                                                              ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                              (=>
                                                                                 (not cmp3$2_0)
                                                                                 (let
                                                                                    ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                                    (=>
                                                                                       (not cmp6$2_0)
                                                                                       (let
                                                                                          ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                                          (=>
                                                                                             (not cmp10$2_0)
                                                                                             (let
                                                                                                ((div$2_0 (div n.addr.0$2_0 10000))
                                                                                                 (add14$2_0 (+ result.0$2_0 4)))
                                                                                                (let
                                                                                                   ((retval1.0$2_0 retval1.0$2_0)
                                                                                                    (b.0$2_0 b.0$2_0)
                                                                                                    (result.0$2_0 add14$2_0)
                                                                                                    (n.addr.0$2_0 div$2_0))
                                                                                                   false)))))))))))))))
                                                      (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    cmp6$1_0
                                    (let
                                       ((inc9$1_0 (+ inc4$1_0 1))
                                        (div10$1_0 (div div5$1_0 10)))
                                       (let
                                          ((cmp11$1_0 (> div10$1_0 0)))
                                          (=>
                                             (not cmp11$1_0)
                                             (let
                                                ((result.0$1_0 inc9$1_0)
                                                 (n.addr.0$1_0 div10$1_0))
                                                (=>
                                                   (and
                                                      (let
                                                         ((b.0$2_0 b.0$2_0_old))
                                                         (let
                                                            ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                             (result.0$2_0 result.0$2_0_old)
                                                             (retval1.0$2_0 retval1.0$2_0_old)
                                                             (cmp$2_0 (= b.0$2_0 0)))
                                                            (let
                                                               ((lnot$2_0 (xor
                                                                              cmp$2_0
                                                                              true)))
                                                               (=>
                                                                  lnot$2_0
                                                                  (let
                                                                     ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                                     (=>
                                                                        cmp2$2_0
                                                                        (let
                                                                           ((retval1.0$2_0 result.0$2_0)
                                                                            (b.0$2_0 0)
                                                                            (result.0$2_0 result.0$2_0)
                                                                            (n.addr.0$2_0 n.addr.0$2_0))
                                                                           false)))))))
                                                      (let
                                                         ((b.0$2_0 b.0$2_0_old))
                                                         (let
                                                            ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                             (result.0$2_0 result.0$2_0_old)
                                                             (retval1.0$2_0 retval1.0$2_0_old)
                                                             (cmp$2_0 (= b.0$2_0 0)))
                                                            (let
                                                               ((lnot$2_0 (xor
                                                                              cmp$2_0
                                                                              true)))
                                                               (=>
                                                                  lnot$2_0
                                                                  (let
                                                                     ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                                     (=>
                                                                        (not cmp2$2_0)
                                                                        (let
                                                                           ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                           (=>
                                                                              cmp3$2_0
                                                                              (let
                                                                                 ((add$2_0 (+ result.0$2_0 1)))
                                                                                 (let
                                                                                    ((retval1.0$2_0 add$2_0)
                                                                                     (b.0$2_0 0)
                                                                                     (result.0$2_0 result.0$2_0)
                                                                                     (n.addr.0$2_0 n.addr.0$2_0))
                                                                                    false))))))))))
                                                      (let
                                                         ((b.0$2_0 b.0$2_0_old))
                                                         (let
                                                            ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                             (result.0$2_0 result.0$2_0_old)
                                                             (retval1.0$2_0 retval1.0$2_0_old)
                                                             (cmp$2_0 (= b.0$2_0 0)))
                                                            (let
                                                               ((lnot$2_0 (xor
                                                                              cmp$2_0
                                                                              true)))
                                                               (=>
                                                                  lnot$2_0
                                                                  (let
                                                                     ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                                     (=>
                                                                        (not cmp2$2_0)
                                                                        (let
                                                                           ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                           (=>
                                                                              (not cmp3$2_0)
                                                                              (let
                                                                                 ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                                 (=>
                                                                                    cmp6$2_0
                                                                                    (let
                                                                                       ((add8$2_0 (+ result.0$2_0 2)))
                                                                                       (let
                                                                                          ((retval1.0$2_0 add8$2_0)
                                                                                           (b.0$2_0 0)
                                                                                           (result.0$2_0 result.0$2_0)
                                                                                           (n.addr.0$2_0 n.addr.0$2_0))
                                                                                          false))))))))))))
                                                      (let
                                                         ((b.0$2_0 b.0$2_0_old))
                                                         (let
                                                            ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                             (result.0$2_0 result.0$2_0_old)
                                                             (retval1.0$2_0 retval1.0$2_0_old)
                                                             (cmp$2_0 (= b.0$2_0 0)))
                                                            (let
                                                               ((lnot$2_0 (xor
                                                                              cmp$2_0
                                                                              true)))
                                                               (=>
                                                                  lnot$2_0
                                                                  (let
                                                                     ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                                     (=>
                                                                        (not cmp2$2_0)
                                                                        (let
                                                                           ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                           (=>
                                                                              (not cmp3$2_0)
                                                                              (let
                                                                                 ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                                 (=>
                                                                                    (not cmp6$2_0)
                                                                                    (let
                                                                                       ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                                       (=>
                                                                                          cmp10$2_0
                                                                                          (let
                                                                                             ((add12$2_0 (+ result.0$2_0 3)))
                                                                                             (let
                                                                                                ((retval1.0$2_0 add12$2_0)
                                                                                                 (b.0$2_0 0)
                                                                                                 (result.0$2_0 result.0$2_0)
                                                                                                 (n.addr.0$2_0 n.addr.0$2_0))
                                                                                                false))))))))))))))
                                                      (let
                                                         ((b.0$2_0 b.0$2_0_old))
                                                         (let
                                                            ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                             (result.0$2_0 result.0$2_0_old)
                                                             (retval1.0$2_0 retval1.0$2_0_old)
                                                             (cmp$2_0 (= b.0$2_0 0)))
                                                            (let
                                                               ((lnot$2_0 (xor
                                                                              cmp$2_0
                                                                              true)))
                                                               (=>
                                                                  lnot$2_0
                                                                  (let
                                                                     ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                                     (=>
                                                                        (not cmp2$2_0)
                                                                        (let
                                                                           ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                           (=>
                                                                              (not cmp3$2_0)
                                                                              (let
                                                                                 ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                                 (=>
                                                                                    (not cmp6$2_0)
                                                                                    (let
                                                                                       ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                                       (=>
                                                                                          (not cmp10$2_0)
                                                                                          (let
                                                                                             ((div$2_0 (div n.addr.0$2_0 10000))
                                                                                              (add14$2_0 (+ result.0$2_0 4)))
                                                                                             (let
                                                                                                ((retval1.0$2_0 retval1.0$2_0)
                                                                                                 (b.0$2_0 b.0$2_0)
                                                                                                 (result.0$2_0 add14$2_0)
                                                                                                 (n.addr.0$2_0 div$2_0))
                                                                                                false)))))))))))))))
                                                   (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((inc4$1_0 (+ inc$1_0 1))
                               (div5$1_0 (div div1$1_0 10)))
                              (let
                                 ((cmp6$1_0 (> div5$1_0 0)))
                                 (=>
                                    (not cmp6$1_0)
                                    (let
                                       ((result.0$1_0 inc4$1_0)
                                        (n.addr.0$1_0 div5$1_0))
                                       (=>
                                          (and
                                             (let
                                                ((b.0$2_0 b.0$2_0_old))
                                                (let
                                                   ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                    (result.0$2_0 result.0$2_0_old)
                                                    (retval1.0$2_0 retval1.0$2_0_old)
                                                    (cmp$2_0 (= b.0$2_0 0)))
                                                   (let
                                                      ((lnot$2_0 (xor
                                                                     cmp$2_0
                                                                     true)))
                                                      (=>
                                                         lnot$2_0
                                                         (let
                                                            ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                            (=>
                                                               cmp2$2_0
                                                               (let
                                                                  ((retval1.0$2_0 result.0$2_0)
                                                                   (b.0$2_0 0)
                                                                   (result.0$2_0 result.0$2_0)
                                                                   (n.addr.0$2_0 n.addr.0$2_0))
                                                                  false)))))))
                                             (let
                                                ((b.0$2_0 b.0$2_0_old))
                                                (let
                                                   ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                    (result.0$2_0 result.0$2_0_old)
                                                    (retval1.0$2_0 retval1.0$2_0_old)
                                                    (cmp$2_0 (= b.0$2_0 0)))
                                                   (let
                                                      ((lnot$2_0 (xor
                                                                     cmp$2_0
                                                                     true)))
                                                      (=>
                                                         lnot$2_0
                                                         (let
                                                            ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                            (=>
                                                               (not cmp2$2_0)
                                                               (let
                                                                  ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                  (=>
                                                                     cmp3$2_0
                                                                     (let
                                                                        ((add$2_0 (+ result.0$2_0 1)))
                                                                        (let
                                                                           ((retval1.0$2_0 add$2_0)
                                                                            (b.0$2_0 0)
                                                                            (result.0$2_0 result.0$2_0)
                                                                            (n.addr.0$2_0 n.addr.0$2_0))
                                                                           false))))))))))
                                             (let
                                                ((b.0$2_0 b.0$2_0_old))
                                                (let
                                                   ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                    (result.0$2_0 result.0$2_0_old)
                                                    (retval1.0$2_0 retval1.0$2_0_old)
                                                    (cmp$2_0 (= b.0$2_0 0)))
                                                   (let
                                                      ((lnot$2_0 (xor
                                                                     cmp$2_0
                                                                     true)))
                                                      (=>
                                                         lnot$2_0
                                                         (let
                                                            ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                            (=>
                                                               (not cmp2$2_0)
                                                               (let
                                                                  ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                  (=>
                                                                     (not cmp3$2_0)
                                                                     (let
                                                                        ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                        (=>
                                                                           cmp6$2_0
                                                                           (let
                                                                              ((add8$2_0 (+ result.0$2_0 2)))
                                                                              (let
                                                                                 ((retval1.0$2_0 add8$2_0)
                                                                                  (b.0$2_0 0)
                                                                                  (result.0$2_0 result.0$2_0)
                                                                                  (n.addr.0$2_0 n.addr.0$2_0))
                                                                                 false))))))))))))
                                             (let
                                                ((b.0$2_0 b.0$2_0_old))
                                                (let
                                                   ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                    (result.0$2_0 result.0$2_0_old)
                                                    (retval1.0$2_0 retval1.0$2_0_old)
                                                    (cmp$2_0 (= b.0$2_0 0)))
                                                   (let
                                                      ((lnot$2_0 (xor
                                                                     cmp$2_0
                                                                     true)))
                                                      (=>
                                                         lnot$2_0
                                                         (let
                                                            ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                            (=>
                                                               (not cmp2$2_0)
                                                               (let
                                                                  ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                  (=>
                                                                     (not cmp3$2_0)
                                                                     (let
                                                                        ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                        (=>
                                                                           (not cmp6$2_0)
                                                                           (let
                                                                              ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                              (=>
                                                                                 cmp10$2_0
                                                                                 (let
                                                                                    ((add12$2_0 (+ result.0$2_0 3)))
                                                                                    (let
                                                                                       ((retval1.0$2_0 add12$2_0)
                                                                                        (b.0$2_0 0)
                                                                                        (result.0$2_0 result.0$2_0)
                                                                                        (n.addr.0$2_0 n.addr.0$2_0))
                                                                                       false))))))))))))))
                                             (let
                                                ((b.0$2_0 b.0$2_0_old))
                                                (let
                                                   ((n.addr.0$2_0 n.addr.0$2_0_old)
                                                    (result.0$2_0 result.0$2_0_old)
                                                    (retval1.0$2_0 retval1.0$2_0_old)
                                                    (cmp$2_0 (= b.0$2_0 0)))
                                                   (let
                                                      ((lnot$2_0 (xor
                                                                     cmp$2_0
                                                                     true)))
                                                      (=>
                                                         lnot$2_0
                                                         (let
                                                            ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                            (=>
                                                               (not cmp2$2_0)
                                                               (let
                                                                  ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                                  (=>
                                                                     (not cmp3$2_0)
                                                                     (let
                                                                        ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                                        (=>
                                                                           (not cmp6$2_0)
                                                                           (let
                                                                              ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                              (=>
                                                                                 (not cmp10$2_0)
                                                                                 (let
                                                                                    ((div$2_0 (div n.addr.0$2_0 10000))
                                                                                     (add14$2_0 (+ result.0$2_0 4)))
                                                                                    (let
                                                                                       ((retval1.0$2_0 retval1.0$2_0)
                                                                                        (b.0$2_0 b.0$2_0)
                                                                                        (result.0$2_0 add14$2_0)
                                                                                        (n.addr.0$2_0 div$2_0))
                                                                                       false)))))))))))))))
                                          (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((result.0$1_0 result.0$1_0_old)
                (cmp$1_0 (> n.addr.0$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ result.0$1_0 1))
                      (div1$1_0 (div n.addr.0$1_0 10)))
                     (let
                        ((cmp2$1_0 (> div1$1_0 0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((result.0$1_0 inc$1_0)
                               (n.addr.0$1_0 div1$1_0))
                              (=>
                                 (and
                                    (let
                                       ((b.0$2_0 b.0$2_0_old))
                                       (let
                                          ((n.addr.0$2_0 n.addr.0$2_0_old)
                                           (result.0$2_0 result.0$2_0_old)
                                           (retval1.0$2_0 retval1.0$2_0_old)
                                           (cmp$2_0 (= b.0$2_0 0)))
                                          (let
                                             ((lnot$2_0 (xor
                                                            cmp$2_0
                                                            true)))
                                             (=>
                                                lnot$2_0
                                                (let
                                                   ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                   (=>
                                                      cmp2$2_0
                                                      (let
                                                         ((retval1.0$2_0 result.0$2_0)
                                                          (b.0$2_0 0)
                                                          (result.0$2_0 result.0$2_0)
                                                          (n.addr.0$2_0 n.addr.0$2_0))
                                                         false)))))))
                                    (let
                                       ((b.0$2_0 b.0$2_0_old))
                                       (let
                                          ((n.addr.0$2_0 n.addr.0$2_0_old)
                                           (result.0$2_0 result.0$2_0_old)
                                           (retval1.0$2_0 retval1.0$2_0_old)
                                           (cmp$2_0 (= b.0$2_0 0)))
                                          (let
                                             ((lnot$2_0 (xor
                                                            cmp$2_0
                                                            true)))
                                             (=>
                                                lnot$2_0
                                                (let
                                                   ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                   (=>
                                                      (not cmp2$2_0)
                                                      (let
                                                         ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                         (=>
                                                            cmp3$2_0
                                                            (let
                                                               ((add$2_0 (+ result.0$2_0 1)))
                                                               (let
                                                                  ((retval1.0$2_0 add$2_0)
                                                                   (b.0$2_0 0)
                                                                   (result.0$2_0 result.0$2_0)
                                                                   (n.addr.0$2_0 n.addr.0$2_0))
                                                                  false))))))))))
                                    (let
                                       ((b.0$2_0 b.0$2_0_old))
                                       (let
                                          ((n.addr.0$2_0 n.addr.0$2_0_old)
                                           (result.0$2_0 result.0$2_0_old)
                                           (retval1.0$2_0 retval1.0$2_0_old)
                                           (cmp$2_0 (= b.0$2_0 0)))
                                          (let
                                             ((lnot$2_0 (xor
                                                            cmp$2_0
                                                            true)))
                                             (=>
                                                lnot$2_0
                                                (let
                                                   ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                   (=>
                                                      (not cmp2$2_0)
                                                      (let
                                                         ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                         (=>
                                                            (not cmp3$2_0)
                                                            (let
                                                               ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                               (=>
                                                                  cmp6$2_0
                                                                  (let
                                                                     ((add8$2_0 (+ result.0$2_0 2)))
                                                                     (let
                                                                        ((retval1.0$2_0 add8$2_0)
                                                                         (b.0$2_0 0)
                                                                         (result.0$2_0 result.0$2_0)
                                                                         (n.addr.0$2_0 n.addr.0$2_0))
                                                                        false))))))))))))
                                    (let
                                       ((b.0$2_0 b.0$2_0_old))
                                       (let
                                          ((n.addr.0$2_0 n.addr.0$2_0_old)
                                           (result.0$2_0 result.0$2_0_old)
                                           (retval1.0$2_0 retval1.0$2_0_old)
                                           (cmp$2_0 (= b.0$2_0 0)))
                                          (let
                                             ((lnot$2_0 (xor
                                                            cmp$2_0
                                                            true)))
                                             (=>
                                                lnot$2_0
                                                (let
                                                   ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                   (=>
                                                      (not cmp2$2_0)
                                                      (let
                                                         ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                         (=>
                                                            (not cmp3$2_0)
                                                            (let
                                                               ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                               (=>
                                                                  (not cmp6$2_0)
                                                                  (let
                                                                     ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                     (=>
                                                                        cmp10$2_0
                                                                        (let
                                                                           ((add12$2_0 (+ result.0$2_0 3)))
                                                                           (let
                                                                              ((retval1.0$2_0 add12$2_0)
                                                                               (b.0$2_0 0)
                                                                               (result.0$2_0 result.0$2_0)
                                                                               (n.addr.0$2_0 n.addr.0$2_0))
                                                                              false))))))))))))))
                                    (let
                                       ((b.0$2_0 b.0$2_0_old))
                                       (let
                                          ((n.addr.0$2_0 n.addr.0$2_0_old)
                                           (result.0$2_0 result.0$2_0_old)
                                           (retval1.0$2_0 retval1.0$2_0_old)
                                           (cmp$2_0 (= b.0$2_0 0)))
                                          (let
                                             ((lnot$2_0 (xor
                                                            cmp$2_0
                                                            true)))
                                             (=>
                                                lnot$2_0
                                                (let
                                                   ((cmp2$2_0 (< n.addr.0$2_0 10)))
                                                   (=>
                                                      (not cmp2$2_0)
                                                      (let
                                                         ((cmp3$2_0 (< n.addr.0$2_0 100)))
                                                         (=>
                                                            (not cmp3$2_0)
                                                            (let
                                                               ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                                               (=>
                                                                  (not cmp6$2_0)
                                                                  (let
                                                                     ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                                                     (=>
                                                                        (not cmp10$2_0)
                                                                        (let
                                                                           ((div$2_0 (div n.addr.0$2_0 10000))
                                                                            (add14$2_0 (+ result.0$2_0 4)))
                                                                           (let
                                                                              ((retval1.0$2_0 retval1.0$2_0)
                                                                               (b.0$2_0 b.0$2_0)
                                                                               (result.0$2_0 add14$2_0)
                                                                               (n.addr.0$2_0 div$2_0))
                                                                              false)))))))))))))))
                                 (INV_MAIN_42 n.addr.0$1_0 result.0$1_0 b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((b.0$2_0 b.0$2_0_old))
            (let
               ((n.addr.0$2_0 n.addr.0$2_0_old)
                (result.0$2_0 result.0$2_0_old)
                (retval1.0$2_0 retval1.0$2_0_old)
                (cmp$2_0 (= b.0$2_0 0)))
               (let
                  ((lnot$2_0 (xor
                                 cmp$2_0
                                 true)))
                  (=>
                     lnot$2_0
                     (let
                        ((cmp2$2_0 (< n.addr.0$2_0 10)))
                        (=>
                           cmp2$2_0
                           (let
                              ((retval1.0$2_0 result.0$2_0)
                               (b.0$2_0 0)
                               (result.0$2_0 result.0$2_0)
                               (n.addr.0$2_0 n.addr.0$2_0))
                              (=>
                                 (and
                                    (let
                                       ((n.addr.0$1_0 n.addr.0$1_0_old))
                                       (let
                                          ((result.0$1_0 result.0$1_0_old)
                                           (cmp$1_0 (> n.addr.0$1_0 0)))
                                          (=>
                                             cmp$1_0
                                             (let
                                                ((inc$1_0 (+ result.0$1_0 1))
                                                 (div1$1_0 (div n.addr.0$1_0 10)))
                                                (let
                                                   ((cmp2$1_0 (> div1$1_0 0)))
                                                   (=>
                                                      cmp2$1_0
                                                      (let
                                                         ((inc4$1_0 (+ inc$1_0 1))
                                                          (div5$1_0 (div div1$1_0 10)))
                                                         (let
                                                            ((cmp6$1_0 (> div5$1_0 0)))
                                                            (=>
                                                               cmp6$1_0
                                                               (let
                                                                  ((inc9$1_0 (+ inc4$1_0 1))
                                                                   (div10$1_0 (div div5$1_0 10)))
                                                                  (let
                                                                     ((cmp11$1_0 (> div10$1_0 0)))
                                                                     (=>
                                                                        cmp11$1_0
                                                                        (let
                                                                           ((inc14$1_0 (+ inc9$1_0 1))
                                                                            (div15$1_0 (div div10$1_0 10)))
                                                                           (let
                                                                              ((result.0$1_0 inc14$1_0)
                                                                               (n.addr.0$1_0 div15$1_0))
                                                                              false))))))))))))))
                                    (let
                                       ((n.addr.0$1_0 n.addr.0$1_0_old))
                                       (let
                                          ((result.0$1_0 result.0$1_0_old)
                                           (cmp$1_0 (> n.addr.0$1_0 0)))
                                          (=>
                                             cmp$1_0
                                             (let
                                                ((inc$1_0 (+ result.0$1_0 1))
                                                 (div1$1_0 (div n.addr.0$1_0 10)))
                                                (let
                                                   ((cmp2$1_0 (> div1$1_0 0)))
                                                   (=>
                                                      cmp2$1_0
                                                      (let
                                                         ((inc4$1_0 (+ inc$1_0 1))
                                                          (div5$1_0 (div div1$1_0 10)))
                                                         (let
                                                            ((cmp6$1_0 (> div5$1_0 0)))
                                                            (=>
                                                               cmp6$1_0
                                                               (let
                                                                  ((inc9$1_0 (+ inc4$1_0 1))
                                                                   (div10$1_0 (div div5$1_0 10)))
                                                                  (let
                                                                     ((cmp11$1_0 (> div10$1_0 0)))
                                                                     (=>
                                                                        (not cmp11$1_0)
                                                                        (let
                                                                           ((result.0$1_0 inc9$1_0)
                                                                            (n.addr.0$1_0 div10$1_0))
                                                                           false)))))))))))))
                                    (let
                                       ((n.addr.0$1_0 n.addr.0$1_0_old))
                                       (let
                                          ((result.0$1_0 result.0$1_0_old)
                                           (cmp$1_0 (> n.addr.0$1_0 0)))
                                          (=>
                                             cmp$1_0
                                             (let
                                                ((inc$1_0 (+ result.0$1_0 1))
                                                 (div1$1_0 (div n.addr.0$1_0 10)))
                                                (let
                                                   ((cmp2$1_0 (> div1$1_0 0)))
                                                   (=>
                                                      cmp2$1_0
                                                      (let
                                                         ((inc4$1_0 (+ inc$1_0 1))
                                                          (div5$1_0 (div div1$1_0 10)))
                                                         (let
                                                            ((cmp6$1_0 (> div5$1_0 0)))
                                                            (=>
                                                               (not cmp6$1_0)
                                                               (let
                                                                  ((result.0$1_0 inc4$1_0)
                                                                   (n.addr.0$1_0 div5$1_0))
                                                                  false))))))))))
                                    (let
                                       ((n.addr.0$1_0 n.addr.0$1_0_old))
                                       (let
                                          ((result.0$1_0 result.0$1_0_old)
                                           (cmp$1_0 (> n.addr.0$1_0 0)))
                                          (=>
                                             cmp$1_0
                                             (let
                                                ((inc$1_0 (+ result.0$1_0 1))
                                                 (div1$1_0 (div n.addr.0$1_0 10)))
                                                (let
                                                   ((cmp2$1_0 (> div1$1_0 0)))
                                                   (=>
                                                      (not cmp2$1_0)
                                                      (let
                                                         ((result.0$1_0 inc$1_0)
                                                          (n.addr.0$1_0 div1$1_0))
                                                         false))))))))
                                 (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((b.0$2_0 b.0$2_0_old))
            (let
               ((n.addr.0$2_0 n.addr.0$2_0_old)
                (result.0$2_0 result.0$2_0_old)
                (retval1.0$2_0 retval1.0$2_0_old)
                (cmp$2_0 (= b.0$2_0 0)))
               (let
                  ((lnot$2_0 (xor
                                 cmp$2_0
                                 true)))
                  (=>
                     lnot$2_0
                     (let
                        ((cmp2$2_0 (< n.addr.0$2_0 10)))
                        (=>
                           (not cmp2$2_0)
                           (let
                              ((cmp3$2_0 (< n.addr.0$2_0 100)))
                              (=>
                                 cmp3$2_0
                                 (let
                                    ((add$2_0 (+ result.0$2_0 1)))
                                    (let
                                       ((retval1.0$2_0 add$2_0)
                                        (b.0$2_0 0)
                                        (result.0$2_0 result.0$2_0)
                                        (n.addr.0$2_0 n.addr.0$2_0))
                                       (=>
                                          (and
                                             (let
                                                ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                (let
                                                   ((result.0$1_0 result.0$1_0_old)
                                                    (cmp$1_0 (> n.addr.0$1_0 0)))
                                                   (=>
                                                      cmp$1_0
                                                      (let
                                                         ((inc$1_0 (+ result.0$1_0 1))
                                                          (div1$1_0 (div n.addr.0$1_0 10)))
                                                         (let
                                                            ((cmp2$1_0 (> div1$1_0 0)))
                                                            (=>
                                                               cmp2$1_0
                                                               (let
                                                                  ((inc4$1_0 (+ inc$1_0 1))
                                                                   (div5$1_0 (div div1$1_0 10)))
                                                                  (let
                                                                     ((cmp6$1_0 (> div5$1_0 0)))
                                                                     (=>
                                                                        cmp6$1_0
                                                                        (let
                                                                           ((inc9$1_0 (+ inc4$1_0 1))
                                                                            (div10$1_0 (div div5$1_0 10)))
                                                                           (let
                                                                              ((cmp11$1_0 (> div10$1_0 0)))
                                                                              (=>
                                                                                 cmp11$1_0
                                                                                 (let
                                                                                    ((inc14$1_0 (+ inc9$1_0 1))
                                                                                     (div15$1_0 (div div10$1_0 10)))
                                                                                    (let
                                                                                       ((result.0$1_0 inc14$1_0)
                                                                                        (n.addr.0$1_0 div15$1_0))
                                                                                       false))))))))))))))
                                             (let
                                                ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                (let
                                                   ((result.0$1_0 result.0$1_0_old)
                                                    (cmp$1_0 (> n.addr.0$1_0 0)))
                                                   (=>
                                                      cmp$1_0
                                                      (let
                                                         ((inc$1_0 (+ result.0$1_0 1))
                                                          (div1$1_0 (div n.addr.0$1_0 10)))
                                                         (let
                                                            ((cmp2$1_0 (> div1$1_0 0)))
                                                            (=>
                                                               cmp2$1_0
                                                               (let
                                                                  ((inc4$1_0 (+ inc$1_0 1))
                                                                   (div5$1_0 (div div1$1_0 10)))
                                                                  (let
                                                                     ((cmp6$1_0 (> div5$1_0 0)))
                                                                     (=>
                                                                        cmp6$1_0
                                                                        (let
                                                                           ((inc9$1_0 (+ inc4$1_0 1))
                                                                            (div10$1_0 (div div5$1_0 10)))
                                                                           (let
                                                                              ((cmp11$1_0 (> div10$1_0 0)))
                                                                              (=>
                                                                                 (not cmp11$1_0)
                                                                                 (let
                                                                                    ((result.0$1_0 inc9$1_0)
                                                                                     (n.addr.0$1_0 div10$1_0))
                                                                                    false)))))))))))))
                                             (let
                                                ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                (let
                                                   ((result.0$1_0 result.0$1_0_old)
                                                    (cmp$1_0 (> n.addr.0$1_0 0)))
                                                   (=>
                                                      cmp$1_0
                                                      (let
                                                         ((inc$1_0 (+ result.0$1_0 1))
                                                          (div1$1_0 (div n.addr.0$1_0 10)))
                                                         (let
                                                            ((cmp2$1_0 (> div1$1_0 0)))
                                                            (=>
                                                               cmp2$1_0
                                                               (let
                                                                  ((inc4$1_0 (+ inc$1_0 1))
                                                                   (div5$1_0 (div div1$1_0 10)))
                                                                  (let
                                                                     ((cmp6$1_0 (> div5$1_0 0)))
                                                                     (=>
                                                                        (not cmp6$1_0)
                                                                        (let
                                                                           ((result.0$1_0 inc4$1_0)
                                                                            (n.addr.0$1_0 div5$1_0))
                                                                           false))))))))))
                                             (let
                                                ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                (let
                                                   ((result.0$1_0 result.0$1_0_old)
                                                    (cmp$1_0 (> n.addr.0$1_0 0)))
                                                   (=>
                                                      cmp$1_0
                                                      (let
                                                         ((inc$1_0 (+ result.0$1_0 1))
                                                          (div1$1_0 (div n.addr.0$1_0 10)))
                                                         (let
                                                            ((cmp2$1_0 (> div1$1_0 0)))
                                                            (=>
                                                               (not cmp2$1_0)
                                                               (let
                                                                  ((result.0$1_0 inc$1_0)
                                                                   (n.addr.0$1_0 div1$1_0))
                                                                  false))))))))
                                          (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((b.0$2_0 b.0$2_0_old))
            (let
               ((n.addr.0$2_0 n.addr.0$2_0_old)
                (result.0$2_0 result.0$2_0_old)
                (retval1.0$2_0 retval1.0$2_0_old)
                (cmp$2_0 (= b.0$2_0 0)))
               (let
                  ((lnot$2_0 (xor
                                 cmp$2_0
                                 true)))
                  (=>
                     lnot$2_0
                     (let
                        ((cmp2$2_0 (< n.addr.0$2_0 10)))
                        (=>
                           (not cmp2$2_0)
                           (let
                              ((cmp3$2_0 (< n.addr.0$2_0 100)))
                              (=>
                                 (not cmp3$2_0)
                                 (let
                                    ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                    (=>
                                       cmp6$2_0
                                       (let
                                          ((add8$2_0 (+ result.0$2_0 2)))
                                          (let
                                             ((retval1.0$2_0 add8$2_0)
                                              (b.0$2_0 0)
                                              (result.0$2_0 result.0$2_0)
                                              (n.addr.0$2_0 n.addr.0$2_0))
                                             (=>
                                                (and
                                                   (let
                                                      ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                      (let
                                                         ((result.0$1_0 result.0$1_0_old)
                                                          (cmp$1_0 (> n.addr.0$1_0 0)))
                                                         (=>
                                                            cmp$1_0
                                                            (let
                                                               ((inc$1_0 (+ result.0$1_0 1))
                                                                (div1$1_0 (div n.addr.0$1_0 10)))
                                                               (let
                                                                  ((cmp2$1_0 (> div1$1_0 0)))
                                                                  (=>
                                                                     cmp2$1_0
                                                                     (let
                                                                        ((inc4$1_0 (+ inc$1_0 1))
                                                                         (div5$1_0 (div div1$1_0 10)))
                                                                        (let
                                                                           ((cmp6$1_0 (> div5$1_0 0)))
                                                                           (=>
                                                                              cmp6$1_0
                                                                              (let
                                                                                 ((inc9$1_0 (+ inc4$1_0 1))
                                                                                  (div10$1_0 (div div5$1_0 10)))
                                                                                 (let
                                                                                    ((cmp11$1_0 (> div10$1_0 0)))
                                                                                    (=>
                                                                                       cmp11$1_0
                                                                                       (let
                                                                                          ((inc14$1_0 (+ inc9$1_0 1))
                                                                                           (div15$1_0 (div div10$1_0 10)))
                                                                                          (let
                                                                                             ((result.0$1_0 inc14$1_0)
                                                                                              (n.addr.0$1_0 div15$1_0))
                                                                                             false))))))))))))))
                                                   (let
                                                      ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                      (let
                                                         ((result.0$1_0 result.0$1_0_old)
                                                          (cmp$1_0 (> n.addr.0$1_0 0)))
                                                         (=>
                                                            cmp$1_0
                                                            (let
                                                               ((inc$1_0 (+ result.0$1_0 1))
                                                                (div1$1_0 (div n.addr.0$1_0 10)))
                                                               (let
                                                                  ((cmp2$1_0 (> div1$1_0 0)))
                                                                  (=>
                                                                     cmp2$1_0
                                                                     (let
                                                                        ((inc4$1_0 (+ inc$1_0 1))
                                                                         (div5$1_0 (div div1$1_0 10)))
                                                                        (let
                                                                           ((cmp6$1_0 (> div5$1_0 0)))
                                                                           (=>
                                                                              cmp6$1_0
                                                                              (let
                                                                                 ((inc9$1_0 (+ inc4$1_0 1))
                                                                                  (div10$1_0 (div div5$1_0 10)))
                                                                                 (let
                                                                                    ((cmp11$1_0 (> div10$1_0 0)))
                                                                                    (=>
                                                                                       (not cmp11$1_0)
                                                                                       (let
                                                                                          ((result.0$1_0 inc9$1_0)
                                                                                           (n.addr.0$1_0 div10$1_0))
                                                                                          false)))))))))))))
                                                   (let
                                                      ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                      (let
                                                         ((result.0$1_0 result.0$1_0_old)
                                                          (cmp$1_0 (> n.addr.0$1_0 0)))
                                                         (=>
                                                            cmp$1_0
                                                            (let
                                                               ((inc$1_0 (+ result.0$1_0 1))
                                                                (div1$1_0 (div n.addr.0$1_0 10)))
                                                               (let
                                                                  ((cmp2$1_0 (> div1$1_0 0)))
                                                                  (=>
                                                                     cmp2$1_0
                                                                     (let
                                                                        ((inc4$1_0 (+ inc$1_0 1))
                                                                         (div5$1_0 (div div1$1_0 10)))
                                                                        (let
                                                                           ((cmp6$1_0 (> div5$1_0 0)))
                                                                           (=>
                                                                              (not cmp6$1_0)
                                                                              (let
                                                                                 ((result.0$1_0 inc4$1_0)
                                                                                  (n.addr.0$1_0 div5$1_0))
                                                                                 false))))))))))
                                                   (let
                                                      ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                      (let
                                                         ((result.0$1_0 result.0$1_0_old)
                                                          (cmp$1_0 (> n.addr.0$1_0 0)))
                                                         (=>
                                                            cmp$1_0
                                                            (let
                                                               ((inc$1_0 (+ result.0$1_0 1))
                                                                (div1$1_0 (div n.addr.0$1_0 10)))
                                                               (let
                                                                  ((cmp2$1_0 (> div1$1_0 0)))
                                                                  (=>
                                                                     (not cmp2$1_0)
                                                                     (let
                                                                        ((result.0$1_0 inc$1_0)
                                                                         (n.addr.0$1_0 div1$1_0))
                                                                        false))))))))
                                                (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((b.0$2_0 b.0$2_0_old))
            (let
               ((n.addr.0$2_0 n.addr.0$2_0_old)
                (result.0$2_0 result.0$2_0_old)
                (retval1.0$2_0 retval1.0$2_0_old)
                (cmp$2_0 (= b.0$2_0 0)))
               (let
                  ((lnot$2_0 (xor
                                 cmp$2_0
                                 true)))
                  (=>
                     lnot$2_0
                     (let
                        ((cmp2$2_0 (< n.addr.0$2_0 10)))
                        (=>
                           (not cmp2$2_0)
                           (let
                              ((cmp3$2_0 (< n.addr.0$2_0 100)))
                              (=>
                                 (not cmp3$2_0)
                                 (let
                                    ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                    (=>
                                       (not cmp6$2_0)
                                       (let
                                          ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                          (=>
                                             cmp10$2_0
                                             (let
                                                ((add12$2_0 (+ result.0$2_0 3)))
                                                (let
                                                   ((retval1.0$2_0 add12$2_0)
                                                    (b.0$2_0 0)
                                                    (result.0$2_0 result.0$2_0)
                                                    (n.addr.0$2_0 n.addr.0$2_0))
                                                   (=>
                                                      (and
                                                         (let
                                                            ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                            (let
                                                               ((result.0$1_0 result.0$1_0_old)
                                                                (cmp$1_0 (> n.addr.0$1_0 0)))
                                                               (=>
                                                                  cmp$1_0
                                                                  (let
                                                                     ((inc$1_0 (+ result.0$1_0 1))
                                                                      (div1$1_0 (div n.addr.0$1_0 10)))
                                                                     (let
                                                                        ((cmp2$1_0 (> div1$1_0 0)))
                                                                        (=>
                                                                           cmp2$1_0
                                                                           (let
                                                                              ((inc4$1_0 (+ inc$1_0 1))
                                                                               (div5$1_0 (div div1$1_0 10)))
                                                                              (let
                                                                                 ((cmp6$1_0 (> div5$1_0 0)))
                                                                                 (=>
                                                                                    cmp6$1_0
                                                                                    (let
                                                                                       ((inc9$1_0 (+ inc4$1_0 1))
                                                                                        (div10$1_0 (div div5$1_0 10)))
                                                                                       (let
                                                                                          ((cmp11$1_0 (> div10$1_0 0)))
                                                                                          (=>
                                                                                             cmp11$1_0
                                                                                             (let
                                                                                                ((inc14$1_0 (+ inc9$1_0 1))
                                                                                                 (div15$1_0 (div div10$1_0 10)))
                                                                                                (let
                                                                                                   ((result.0$1_0 inc14$1_0)
                                                                                                    (n.addr.0$1_0 div15$1_0))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                            (let
                                                               ((result.0$1_0 result.0$1_0_old)
                                                                (cmp$1_0 (> n.addr.0$1_0 0)))
                                                               (=>
                                                                  cmp$1_0
                                                                  (let
                                                                     ((inc$1_0 (+ result.0$1_0 1))
                                                                      (div1$1_0 (div n.addr.0$1_0 10)))
                                                                     (let
                                                                        ((cmp2$1_0 (> div1$1_0 0)))
                                                                        (=>
                                                                           cmp2$1_0
                                                                           (let
                                                                              ((inc4$1_0 (+ inc$1_0 1))
                                                                               (div5$1_0 (div div1$1_0 10)))
                                                                              (let
                                                                                 ((cmp6$1_0 (> div5$1_0 0)))
                                                                                 (=>
                                                                                    cmp6$1_0
                                                                                    (let
                                                                                       ((inc9$1_0 (+ inc4$1_0 1))
                                                                                        (div10$1_0 (div div5$1_0 10)))
                                                                                       (let
                                                                                          ((cmp11$1_0 (> div10$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp11$1_0)
                                                                                             (let
                                                                                                ((result.0$1_0 inc9$1_0)
                                                                                                 (n.addr.0$1_0 div10$1_0))
                                                                                                false)))))))))))))
                                                         (let
                                                            ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                            (let
                                                               ((result.0$1_0 result.0$1_0_old)
                                                                (cmp$1_0 (> n.addr.0$1_0 0)))
                                                               (=>
                                                                  cmp$1_0
                                                                  (let
                                                                     ((inc$1_0 (+ result.0$1_0 1))
                                                                      (div1$1_0 (div n.addr.0$1_0 10)))
                                                                     (let
                                                                        ((cmp2$1_0 (> div1$1_0 0)))
                                                                        (=>
                                                                           cmp2$1_0
                                                                           (let
                                                                              ((inc4$1_0 (+ inc$1_0 1))
                                                                               (div5$1_0 (div div1$1_0 10)))
                                                                              (let
                                                                                 ((cmp6$1_0 (> div5$1_0 0)))
                                                                                 (=>
                                                                                    (not cmp6$1_0)
                                                                                    (let
                                                                                       ((result.0$1_0 inc4$1_0)
                                                                                        (n.addr.0$1_0 div5$1_0))
                                                                                       false))))))))))
                                                         (let
                                                            ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                            (let
                                                               ((result.0$1_0 result.0$1_0_old)
                                                                (cmp$1_0 (> n.addr.0$1_0 0)))
                                                               (=>
                                                                  cmp$1_0
                                                                  (let
                                                                     ((inc$1_0 (+ result.0$1_0 1))
                                                                      (div1$1_0 (div n.addr.0$1_0 10)))
                                                                     (let
                                                                        ((cmp2$1_0 (> div1$1_0 0)))
                                                                        (=>
                                                                           (not cmp2$1_0)
                                                                           (let
                                                                              ((result.0$1_0 inc$1_0)
                                                                               (n.addr.0$1_0 div1$1_0))
                                                                              false))))))))
                                                      (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))))
(assert
   (forall
      ((n.addr.0$1_0_old Int)
       (result.0$1_0_old Int)
       (b.0$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval1.0$2_0_old Int))
      (=>
         (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0_old n.addr.0$2_0_old result.0$2_0_old retval1.0$2_0_old)
         (let
            ((b.0$2_0 b.0$2_0_old))
            (let
               ((n.addr.0$2_0 n.addr.0$2_0_old)
                (result.0$2_0 result.0$2_0_old)
                (retval1.0$2_0 retval1.0$2_0_old)
                (cmp$2_0 (= b.0$2_0 0)))
               (let
                  ((lnot$2_0 (xor
                                 cmp$2_0
                                 true)))
                  (=>
                     lnot$2_0
                     (let
                        ((cmp2$2_0 (< n.addr.0$2_0 10)))
                        (=>
                           (not cmp2$2_0)
                           (let
                              ((cmp3$2_0 (< n.addr.0$2_0 100)))
                              (=>
                                 (not cmp3$2_0)
                                 (let
                                    ((cmp6$2_0 (< n.addr.0$2_0 1000)))
                                    (=>
                                       (not cmp6$2_0)
                                       (let
                                          ((cmp10$2_0 (< n.addr.0$2_0 10000)))
                                          (=>
                                             (not cmp10$2_0)
                                             (let
                                                ((div$2_0 (div n.addr.0$2_0 10000))
                                                 (add14$2_0 (+ result.0$2_0 4)))
                                                (let
                                                   ((retval1.0$2_0 retval1.0$2_0)
                                                    (b.0$2_0 b.0$2_0)
                                                    (result.0$2_0 add14$2_0)
                                                    (n.addr.0$2_0 div$2_0))
                                                   (=>
                                                      (and
                                                         (let
                                                            ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                            (let
                                                               ((result.0$1_0 result.0$1_0_old)
                                                                (cmp$1_0 (> n.addr.0$1_0 0)))
                                                               (=>
                                                                  cmp$1_0
                                                                  (let
                                                                     ((inc$1_0 (+ result.0$1_0 1))
                                                                      (div1$1_0 (div n.addr.0$1_0 10)))
                                                                     (let
                                                                        ((cmp2$1_0 (> div1$1_0 0)))
                                                                        (=>
                                                                           cmp2$1_0
                                                                           (let
                                                                              ((inc4$1_0 (+ inc$1_0 1))
                                                                               (div5$1_0 (div div1$1_0 10)))
                                                                              (let
                                                                                 ((cmp6$1_0 (> div5$1_0 0)))
                                                                                 (=>
                                                                                    cmp6$1_0
                                                                                    (let
                                                                                       ((inc9$1_0 (+ inc4$1_0 1))
                                                                                        (div10$1_0 (div div5$1_0 10)))
                                                                                       (let
                                                                                          ((cmp11$1_0 (> div10$1_0 0)))
                                                                                          (=>
                                                                                             cmp11$1_0
                                                                                             (let
                                                                                                ((inc14$1_0 (+ inc9$1_0 1))
                                                                                                 (div15$1_0 (div div10$1_0 10)))
                                                                                                (let
                                                                                                   ((result.0$1_0 inc14$1_0)
                                                                                                    (n.addr.0$1_0 div15$1_0))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                            (let
                                                               ((result.0$1_0 result.0$1_0_old)
                                                                (cmp$1_0 (> n.addr.0$1_0 0)))
                                                               (=>
                                                                  cmp$1_0
                                                                  (let
                                                                     ((inc$1_0 (+ result.0$1_0 1))
                                                                      (div1$1_0 (div n.addr.0$1_0 10)))
                                                                     (let
                                                                        ((cmp2$1_0 (> div1$1_0 0)))
                                                                        (=>
                                                                           cmp2$1_0
                                                                           (let
                                                                              ((inc4$1_0 (+ inc$1_0 1))
                                                                               (div5$1_0 (div div1$1_0 10)))
                                                                              (let
                                                                                 ((cmp6$1_0 (> div5$1_0 0)))
                                                                                 (=>
                                                                                    cmp6$1_0
                                                                                    (let
                                                                                       ((inc9$1_0 (+ inc4$1_0 1))
                                                                                        (div10$1_0 (div div5$1_0 10)))
                                                                                       (let
                                                                                          ((cmp11$1_0 (> div10$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp11$1_0)
                                                                                             (let
                                                                                                ((result.0$1_0 inc9$1_0)
                                                                                                 (n.addr.0$1_0 div10$1_0))
                                                                                                false)))))))))))))
                                                         (let
                                                            ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                            (let
                                                               ((result.0$1_0 result.0$1_0_old)
                                                                (cmp$1_0 (> n.addr.0$1_0 0)))
                                                               (=>
                                                                  cmp$1_0
                                                                  (let
                                                                     ((inc$1_0 (+ result.0$1_0 1))
                                                                      (div1$1_0 (div n.addr.0$1_0 10)))
                                                                     (let
                                                                        ((cmp2$1_0 (> div1$1_0 0)))
                                                                        (=>
                                                                           cmp2$1_0
                                                                           (let
                                                                              ((inc4$1_0 (+ inc$1_0 1))
                                                                               (div5$1_0 (div div1$1_0 10)))
                                                                              (let
                                                                                 ((cmp6$1_0 (> div5$1_0 0)))
                                                                                 (=>
                                                                                    (not cmp6$1_0)
                                                                                    (let
                                                                                       ((result.0$1_0 inc4$1_0)
                                                                                        (n.addr.0$1_0 div5$1_0))
                                                                                       false))))))))))
                                                         (let
                                                            ((n.addr.0$1_0 n.addr.0$1_0_old))
                                                            (let
                                                               ((result.0$1_0 result.0$1_0_old)
                                                                (cmp$1_0 (> n.addr.0$1_0 0)))
                                                               (=>
                                                                  cmp$1_0
                                                                  (let
                                                                     ((inc$1_0 (+ result.0$1_0 1))
                                                                      (div1$1_0 (div n.addr.0$1_0 10)))
                                                                     (let
                                                                        ((cmp2$1_0 (> div1$1_0 0)))
                                                                        (=>
                                                                           (not cmp2$1_0)
                                                                           (let
                                                                              ((result.0$1_0 inc$1_0)
                                                                               (n.addr.0$1_0 div1$1_0))
                                                                              false))))))))
                                                      (INV_MAIN_42 n.addr.0$1_0_old result.0$1_0_old b.0$2_0 n.addr.0$2_0 result.0$2_0 retval1.0$2_0)))))))))))))))))))
(check-sat)
(get-model)
