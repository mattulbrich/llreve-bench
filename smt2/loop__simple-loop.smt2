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
; :annot (INV_MAIN_42 i.0$1_0 i.0$2_0)
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
             (i.0$1_0 0)
             (z$2_0 z$2_0_old)
             (i.0$2_0 1))
            (INV_MAIN_42 i.0$1_0 i.0$2_0)))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old i.0$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old))
            (let
               ((cmp$1_0 (<= i.0$1_0 10)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 i.0$1_0)
                      (i.0$2_0 i.0$2_0_old))
                     (let
                        ((cmp$2_0 (<= i.0$2_0 10)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((result$2 i.0$2_0))
                              (OUT_INV result$1 result$2)))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old i.0$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old))
            (let
               ((cmp$1_0 (<= i.0$1_0 10)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ i.0$1_0 1)))
                     (let
                        ((i.0$1_0 inc$1_0)
                         (i.0$2_0 i.0$2_0_old))
                        (let
                           ((cmp$2_0 (<= i.0$2_0 10)))
                           (=>
                              cmp$2_0
                              (let
                                 ((inc$2_0 (+ i.0$2_0 1)))
                                 (let
                                    ((i.0$2_0 inc$2_0))
                                    (INV_MAIN_42 i.0$1_0 i.0$2_0)))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old i.0$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old))
            (let
               ((cmp$1_0 (<= i.0$1_0 10)))
               (=>
                  cmp$1_0
                  (let
                     ((inc$1_0 (+ i.0$1_0 1)))
                     (let
                        ((i.0$1_0 inc$1_0))
                        (=>
                           (let
                              ((i.0$2_0 i.0$2_0_old))
                              (let
                                 ((cmp$2_0 (<= i.0$2_0 10)))
                                 (=>
                                    cmp$2_0
                                    (let
                                       ((inc$2_0 (+ i.0$2_0 1)))
                                       (let
                                          ((i.0$2_0 inc$2_0))
                                          false)))))
                           (INV_MAIN_42 i.0$1_0 i.0$2_0_old))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_MAIN_42 i.0$1_0_old i.0$2_0_old)
         (let
            ((i.0$2_0 i.0$2_0_old))
            (let
               ((cmp$2_0 (<= i.0$2_0 10)))
               (=>
                  cmp$2_0
                  (let
                     ((inc$2_0 (+ i.0$2_0 1)))
                     (let
                        ((i.0$2_0 inc$2_0))
                        (=>
                           (let
                              ((i.0$1_0 i.0$1_0_old))
                              (let
                                 ((cmp$1_0 (<= i.0$1_0 10)))
                                 (=>
                                    cmp$1_0
                                    (let
                                       ((inc$1_0 (+ i.0$1_0 1)))
                                       (let
                                          ((i.0$1_0 inc$1_0))
                                          false)))))
                           (INV_MAIN_42 i.0$1_0_old i.0$2_0))))))))))
(check-sat)
(get-model)
