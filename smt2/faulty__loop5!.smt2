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
; :annot (INV_MAIN_42 i.0$1_0 j.0$1_0 n$1_0 i.0$2_0 j.0$2_0)
(declare-fun
   INV_MAIN_42
   (Int
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
            ((n$1_0 n$1_0_old)
             (i.0$1_0 0)
             (j.0$1_0 0)
             (n$2_0 n$2_0_old))
            (let
               ((add$2_0 (+ n$2_0 1)))
               (let
                  ((i.0$2_0 add$2_0)
                   (j.0$2_0 0))
                  (INV_MAIN_42 i.0$1_0 j.0$1_0 n$1_0 i.0$2_0 j.0$2_0)))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0_old j.0$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((add$1_0 (+ n$1_0 n$1_0)))
               (let
                  ((cmp$1_0 (< i.0$1_0 add$1_0)))
                  (=>
                     (not cmp$1_0)
                     (let
                        ((result$1 j.0$1_0)
                         (i.0$2_0 i.0$2_0_old))
                        (let
                           ((j.0$2_0 j.0$2_0_old)
                            (cmp$2_0 (> i.0$2_0 0)))
                           (=>
                              (not cmp$2_0)
                              (let
                                 ((result$2 j.0$2_0))
                                 (OUT_INV result$1 result$2))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0_old j.0$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((add$1_0 (+ n$1_0 n$1_0)))
               (let
                  ((cmp$1_0 (< i.0$1_0 add$1_0)))
                  (=>
                     cmp$1_0
                     (let
                        ((inc$1_0 (+ j.0$1_0 1))
                         (inc1$1_0 (+ i.0$1_0 1)))
                        (let
                           ((i.0$1_0 inc1$1_0)
                            (j.0$1_0 inc$1_0)
                            (i.0$2_0 i.0$2_0_old))
                           (let
                              ((j.0$2_0 j.0$2_0_old)
                               (cmp$2_0 (> i.0$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((add1$2_0 (+ j.0$2_0 2))
                                     (sub$2_0 (- i.0$2_0 1)))
                                    (let
                                       ((i.0$2_0 sub$2_0)
                                        (j.0$2_0 add1$2_0))
                                       (INV_MAIN_42 i.0$1_0 j.0$1_0 n$1_0 i.0$2_0 j.0$2_0))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0_old j.0$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (j.0$1_0 j.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((add$1_0 (+ n$1_0 n$1_0)))
               (let
                  ((cmp$1_0 (< i.0$1_0 add$1_0)))
                  (=>
                     cmp$1_0
                     (let
                        ((inc$1_0 (+ j.0$1_0 1))
                         (inc1$1_0 (+ i.0$1_0 1)))
                        (let
                           ((i.0$1_0 inc1$1_0)
                            (j.0$1_0 inc$1_0))
                           (=>
                              (let
                                 ((i.0$2_0 i.0$2_0_old))
                                 (let
                                    ((j.0$2_0 j.0$2_0_old)
                                     (cmp$2_0 (> i.0$2_0 0)))
                                    (=>
                                       cmp$2_0
                                       (let
                                          ((add1$2_0 (+ j.0$2_0 2))
                                           (sub$2_0 (- i.0$2_0 1)))
                                          (let
                                             ((i.0$2_0 sub$2_0)
                                              (j.0$2_0 add1$2_0))
                                             false)))))
                              (INV_MAIN_42 i.0$1_0 j.0$1_0 n$1_0 i.0$2_0_old j.0$2_0_old)))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0_old j.0$2_0_old)
         (let
            ((i.0$2_0 i.0$2_0_old))
            (let
               ((j.0$2_0 j.0$2_0_old)
                (cmp$2_0 (> i.0$2_0 0)))
               (=>
                  cmp$2_0
                  (let
                     ((add1$2_0 (+ j.0$2_0 2))
                      (sub$2_0 (- i.0$2_0 1)))
                     (let
                        ((i.0$2_0 sub$2_0)
                         (j.0$2_0 add1$2_0))
                        (=>
                           (let
                              ((i.0$1_0 i.0$1_0_old)
                               (j.0$1_0 j.0$1_0_old)
                               (n$1_0 n$1_0_old))
                              (let
                                 ((add$1_0 (+ n$1_0 n$1_0)))
                                 (let
                                    ((cmp$1_0 (< i.0$1_0 add$1_0)))
                                    (=>
                                       cmp$1_0
                                       (let
                                          ((inc$1_0 (+ j.0$1_0 1))
                                           (inc1$1_0 (+ i.0$1_0 1)))
                                          (let
                                             ((i.0$1_0 inc1$1_0)
                                              (j.0$1_0 inc$1_0))
                                             false))))))
                           (INV_MAIN_42 i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0 j.0$2_0))))))))))
(check-sat)
(get-model)
