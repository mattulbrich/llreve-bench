;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((z$1_0 Int)
    (z$2_0 Int))
   Bool
   (= z$1_0 z$2_0))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
; :annot (INV_MAIN_42 x.0$1_0 x.0$2_0)
(declare-fun
   INV_MAIN_42
   (Int
    Int)
   Bool)
(assert
   (forall
      ((z$1_0_old Int)
       (z$2_0_old Int))
      (=>
         (IN_INV z$1_0_old z$2_0_old)
         (let
            ((z$1_0 z$1_0_old)
             (x.0$1_0 1))
            (let
               ((cmp$1_0 (<= x.0$1_0 9)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((mul1$1_0 (* 2 x.0$1_0)))
                     (let
                        ((result$1 mul1$1_0)
                         (z$2_0 z$2_0_old)
                         (x.0$2_0 1))
                        (let
                           ((cmp$2_0 (< x.0$2_0 10)))
                           (not cmp$2_0))))))))))
(assert
   (forall
      ((z$1_0_old Int)
       (z$2_0_old Int))
      (=>
         (IN_INV z$1_0_old z$2_0_old)
         (let
            ((z$1_0 z$1_0_old)
             (x.0$1_0 1))
            (let
               ((cmp$1_0 (<= x.0$1_0 9)))
               (=>
                  cmp$1_0
                  (let
                     ((z$2_0 z$2_0_old)
                      (x.0$2_0 1))
                     (let
                        ((cmp$2_0 (< x.0$2_0 10)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((mul$2_0 (* x.0$2_0 2)))
                              (let
                                 ((result$2 mul$2_0))
                                 false)))))))))))
(assert
   (forall
      ((z$1_0_old Int)
       (z$2_0_old Int))
      (=>
         (IN_INV z$1_0_old z$2_0_old)
         (let
            ((z$1_0 z$1_0_old)
             (x.0$1_0 1))
            (let
               ((cmp$1_0 (<= x.0$1_0 9)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((mul1$1_0 (* 2 x.0$1_0)))
                     (let
                        ((result$1 mul1$1_0)
                         (z$2_0 z$2_0_old)
                         (x.0$2_0 1))
                        (let
                           ((cmp$2_0 (< x.0$2_0 10)))
                           (=>
                              (not cmp$2_0)
                              (let
                                 ((mul$2_0 (* x.0$2_0 2)))
                                 (let
                                    ((result$2 mul$2_0))
                                    (OUT_INV result$1 result$2)))))))))))))
(assert
   (forall
      ((z$1_0_old Int)
       (z$2_0_old Int))
      (=>
         (IN_INV z$1_0_old z$2_0_old)
         (let
            ((z$1_0 z$1_0_old)
             (x.0$1_0 1))
            (let
               ((cmp$1_0 (<= x.0$1_0 9)))
               (=>
                  cmp$1_0
                  (let
                     ((z$2_0 z$2_0_old)
                      (x.0$2_0 1))
                     (let
                        ((cmp$2_0 (< x.0$2_0 10)))
                        (=>
                           cmp$2_0
                           (INV_MAIN_42 x.0$1_0 x.0$2_0))))))))))
(assert
   (forall
      ((x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_42 x.0$1_0_old x.0$2_0_old)
         (let
            ((x.0$1_0 x.0$1_0_old))
            (let
               ((add$1_0 (+ x.0$1_0 2)))
               (let
                  ((mul$1_0 (* 2 add$1_0)))
                  (let
                     ((x.0$1_0 mul$1_0))
                     (let
                        ((cmp$1_0 (<= x.0$1_0 9)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((mul1$1_0 (* 2 x.0$1_0)))
                              (let
                                 ((result$1 mul1$1_0)
                                  (x.0$2_0 x.0$2_0_old))
                                 (let
                                    ((add$2_0 (+ 2 x.0$2_0)))
                                    (let
                                       ((add1$2_0 (+ add$2_0 add$2_0)))
                                       (let
                                          ((x.0$2_0 add1$2_0))
                                          (let
                                             ((cmp$2_0 (< x.0$2_0 10)))
                                             (=>
                                                (not cmp$2_0)
                                                (let
                                                   ((mul$2_0 (* x.0$2_0 2)))
                                                   (let
                                                      ((result$2 mul$2_0))
                                                      (OUT_INV result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_42 x.0$1_0_old x.0$2_0_old)
         (let
            ((x.0$1_0 x.0$1_0_old))
            (let
               ((add$1_0 (+ x.0$1_0 2)))
               (let
                  ((mul$1_0 (* 2 add$1_0)))
                  (let
                     ((x.0$1_0 mul$1_0))
                     (let
                        ((cmp$1_0 (<= x.0$1_0 9)))
                        (=>
                           cmp$1_0
                           (let
                              ((x.0$2_0 x.0$2_0_old))
                              (let
                                 ((add$2_0 (+ 2 x.0$2_0)))
                                 (let
                                    ((add1$2_0 (+ add$2_0 add$2_0)))
                                    (let
                                       ((x.0$2_0 add1$2_0))
                                       (let
                                          ((cmp$2_0 (< x.0$2_0 10)))
                                          (=>
                                             cmp$2_0
                                             (INV_MAIN_42 x.0$1_0 x.0$2_0))))))))))))))))
(assert
   (forall
      ((x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_42 x.0$1_0_old x.0$2_0_old)
         (let
            ((x.0$1_0 x.0$1_0_old))
            (let
               ((add$1_0 (+ x.0$1_0 2)))
               (let
                  ((mul$1_0 (* 2 add$1_0)))
                  (let
                     ((x.0$1_0 mul$1_0))
                     (let
                        ((cmp$1_0 (<= x.0$1_0 9)))
                        (=>
                           cmp$1_0
                           (=>
                              (let
                                 ((x.0$2_0 x.0$2_0_old))
                                 (let
                                    ((add$2_0 (+ 2 x.0$2_0)))
                                    (let
                                       ((add1$2_0 (+ add$2_0 add$2_0)))
                                       (let
                                          ((x.0$2_0 add1$2_0))
                                          (let
                                             ((cmp$2_0 (< x.0$2_0 10)))
                                             (not cmp$2_0))))))
                              (INV_MAIN_42 x.0$1_0 x.0$2_0_old)))))))))))
(assert
   (forall
      ((x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_42 x.0$1_0_old x.0$2_0_old)
         (let
            ((x.0$2_0 x.0$2_0_old))
            (let
               ((add$2_0 (+ 2 x.0$2_0)))
               (let
                  ((add1$2_0 (+ add$2_0 add$2_0)))
                  (let
                     ((x.0$2_0 add1$2_0))
                     (let
                        ((cmp$2_0 (< x.0$2_0 10)))
                        (=>
                           cmp$2_0
                           (=>
                              (let
                                 ((x.0$1_0 x.0$1_0_old))
                                 (let
                                    ((add$1_0 (+ x.0$1_0 2)))
                                    (let
                                       ((mul$1_0 (* 2 add$1_0)))
                                       (let
                                          ((x.0$1_0 mul$1_0))
                                          (let
                                             ((cmp$1_0 (<= x.0$1_0 9)))
                                             (not cmp$1_0))))))
                              (INV_MAIN_42 x.0$1_0_old x.0$2_0)))))))))))
(check-sat)
(get-model)
