;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((t$1_0 Int)
    (c$1_0 Int)
    (r$1_0 Int)
    (t$2_0 Int)
    (c$2_0 Int)
    (r$2_0 Int))
   Bool
   (and
      (= t$1_0 t$2_0)
      (= c$1_0 c$2_0)
      (= r$1_0 r$2_0)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
; :annot (INV_MAIN_13 r.addr.0$1_0 x.2$1_0 r.addr.0$2_0 x.2$2_0)
(declare-fun
   INV_MAIN_13
   (Int
    Int
    Int
    Int)
   Bool)
; :annot (INV_MAIN_23 r$1_0 c.addr.0$2_0 r$2_0 t$2_0 x.0$2_0)
(declare-fun
   INV_MAIN_23
   (Int
    Int
    Int
    Int
    Int)
   Bool)
; :annot (INV_MAIN_42 c.addr.0$1_0 r$1_0 x.0$1_0 c.addr.0$2_0 r$2_0 t$2_0 x.0$2_0)
(declare-fun
   INV_MAIN_42
   (Int
    Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((t$1_0_old Int)
       (c$1_0_old Int)
       (r$1_0_old Int)
       (t$2_0_old Int)
       (c$2_0_old Int)
       (r$2_0_old Int))
      (=>
         (IN_INV t$1_0_old c$1_0_old r$1_0_old t$2_0_old c$2_0_old r$2_0_old)
         (let
            ((t$1_0 t$1_0_old))
            (let
               ((c$1_0 c$1_0_old)
                (r$1_0 r$1_0_old)
                (cmp$1_0 (< 0 t$1_0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((t$2_0 t$2_0_old)
                      (c$2_0 c$2_0_old))
                     (let
                        ((r$2_0 r$2_0_old)
                         (c.addr.0$2_0 c$2_0)
                         (x.0$2_0 0))
                        (INV_MAIN_23 r$1_0 c.addr.0$2_0 r$2_0 t$2_0 x.0$2_0)))))))))
(assert
   (forall
      ((t$1_0_old Int)
       (c$1_0_old Int)
       (r$1_0_old Int)
       (t$2_0_old Int)
       (c$2_0_old Int)
       (r$2_0_old Int))
      (=>
         (IN_INV t$1_0_old c$1_0_old r$1_0_old t$2_0_old c$2_0_old r$2_0_old)
         (let
            ((t$1_0 t$1_0_old))
            (let
               ((c$1_0 c$1_0_old)
                (r$1_0 r$1_0_old)
                (cmp$1_0 (< 0 t$1_0)))
               (=>
                  cmp$1_0
                  (let
                     ((c.addr.0$1_0 c$1_0)
                      (x.0$1_0 0)
                      (t$2_0 t$2_0_old)
                      (c$2_0 c$2_0_old))
                     (let
                        ((r$2_0 r$2_0_old)
                         (c.addr.0$2_0 c$2_0)
                         (x.0$2_0 0))
                        (INV_MAIN_42 c.addr.0$1_0 r$1_0 x.0$1_0 c.addr.0$2_0 r$2_0 t$2_0 x.0$2_0)))))))))
(assert
   (forall
      ((r.addr.0$1_0_old Int)
       (x.2$1_0_old Int)
       (r.addr.0$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_MAIN_13 r.addr.0$1_0_old x.2$1_0_old r.addr.0$2_0_old x.2$2_0_old)
         (let
            ((r.addr.0$1_0 r.addr.0$1_0_old))
            (let
               ((x.2$1_0 x.2$1_0_old)
                (cmp5$1_0 (> r.addr.0$1_0 0)))
               (=>
                  (not cmp5$1_0)
                  (let
                     ((result$1 x.2$1_0)
                      (r.addr.0$2_0 r.addr.0$2_0_old))
                     (let
                        ((x.2$2_0 x.2$2_0_old)
                         (cmp7$2_0 (> r.addr.0$2_0 0)))
                        (=>
                           (not cmp7$2_0)
                           (let
                              ((result$2 x.2$2_0))
                              (OUT_INV result$1 result$2)))))))))))
(assert
   (forall
      ((r.addr.0$1_0_old Int)
       (x.2$1_0_old Int)
       (r.addr.0$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_MAIN_13 r.addr.0$1_0_old x.2$1_0_old r.addr.0$2_0_old x.2$2_0_old)
         (let
            ((r.addr.0$1_0 r.addr.0$1_0_old))
            (let
               ((x.2$1_0 x.2$1_0_old)
                (cmp5$1_0 (> r.addr.0$1_0 0)))
               (=>
                  cmp5$1_0
                  (let
                     ((add$1_0 (+ x.2$1_0 2))
                      (dec10$1_0 (+ r.addr.0$1_0 (- 1))))
                     (let
                        ((r.addr.0$1_0 dec10$1_0)
                         (x.2$1_0 add$1_0)
                         (r.addr.0$2_0 r.addr.0$2_0_old))
                        (let
                           ((x.2$2_0 x.2$2_0_old)
                            (cmp7$2_0 (> r.addr.0$2_0 0)))
                           (=>
                              cmp7$2_0
                              (let
                                 ((add$2_0 (+ x.2$2_0 2))
                                  (dec12$2_0 (+ r.addr.0$2_0 (- 1))))
                                 (let
                                    ((r.addr.0$2_0 dec12$2_0)
                                     (x.2$2_0 add$2_0))
                                    (INV_MAIN_13 r.addr.0$1_0 x.2$1_0 r.addr.0$2_0 x.2$2_0)))))))))))))
(assert
   (forall
      ((r.addr.0$1_0_old Int)
       (x.2$1_0_old Int)
       (r.addr.0$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_MAIN_13 r.addr.0$1_0_old x.2$1_0_old r.addr.0$2_0_old x.2$2_0_old)
         (let
            ((r.addr.0$1_0 r.addr.0$1_0_old))
            (let
               ((x.2$1_0 x.2$1_0_old)
                (cmp5$1_0 (> r.addr.0$1_0 0)))
               (=>
                  cmp5$1_0
                  (let
                     ((add$1_0 (+ x.2$1_0 2))
                      (dec10$1_0 (+ r.addr.0$1_0 (- 1))))
                     (let
                        ((r.addr.0$1_0 dec10$1_0)
                         (x.2$1_0 add$1_0))
                        (=>
                           (let
                              ((r.addr.0$2_0 r.addr.0$2_0_old))
                              (let
                                 ((x.2$2_0 x.2$2_0_old)
                                  (cmp7$2_0 (> r.addr.0$2_0 0)))
                                 (=>
                                    cmp7$2_0
                                    (let
                                       ((add$2_0 (+ x.2$2_0 2))
                                        (dec12$2_0 (+ r.addr.0$2_0 (- 1))))
                                       (let
                                          ((r.addr.0$2_0 dec12$2_0)
                                           (x.2$2_0 add$2_0))
                                          false)))))
                           (INV_MAIN_13 r.addr.0$1_0 x.2$1_0 r.addr.0$2_0_old x.2$2_0_old))))))))))
(assert
   (forall
      ((r.addr.0$1_0_old Int)
       (x.2$1_0_old Int)
       (r.addr.0$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_MAIN_13 r.addr.0$1_0_old x.2$1_0_old r.addr.0$2_0_old x.2$2_0_old)
         (let
            ((r.addr.0$2_0 r.addr.0$2_0_old))
            (let
               ((x.2$2_0 x.2$2_0_old)
                (cmp7$2_0 (> r.addr.0$2_0 0)))
               (=>
                  cmp7$2_0
                  (let
                     ((add$2_0 (+ x.2$2_0 2))
                      (dec12$2_0 (+ r.addr.0$2_0 (- 1))))
                     (let
                        ((r.addr.0$2_0 dec12$2_0)
                         (x.2$2_0 add$2_0))
                        (=>
                           (let
                              ((r.addr.0$1_0 r.addr.0$1_0_old))
                              (let
                                 ((x.2$1_0 x.2$1_0_old)
                                  (cmp5$1_0 (> r.addr.0$1_0 0)))
                                 (=>
                                    cmp5$1_0
                                    (let
                                       ((add$1_0 (+ x.2$1_0 2))
                                        (dec10$1_0 (+ r.addr.0$1_0 (- 1))))
                                       (let
                                          ((r.addr.0$1_0 dec10$1_0)
                                           (x.2$1_0 add$1_0))
                                          false)))))
                           (INV_MAIN_13 r.addr.0$1_0_old x.2$1_0_old r.addr.0$2_0 x.2$2_0))))))))))
(assert
   (forall
      ((r$1_0_old Int)
       (c.addr.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_23 r$1_0_old c.addr.0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((r$1_0 r$1_0_old))
            (let
               ((r.addr.0$1_0 r$1_0)
                (x.2$1_0 0)
                (c.addr.0$2_0 c.addr.0$2_0_old))
               (let
                  ((r$2_0 r$2_0_old)
                   (t$2_0 t$2_0_old)
                   (x.0$2_0 x.0$2_0_old)
                   (cmp$2_0 (< 0 c.addr.0$2_0)))
                  (=>
                     (not cmp$2_0)
                     (let
                        ((r.addr.0$2_0 r$2_0)
                         (x.2$2_0 x.0$2_0))
                        (INV_MAIN_13 r.addr.0$1_0 x.2$1_0 r.addr.0$2_0 x.2$2_0)))))))))
(assert
   (forall
      ((r$1_0_old Int)
       (c.addr.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_23 r$1_0_old c.addr.0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((c.addr.0$2_0 c.addr.0$2_0_old))
            (let
               ((r$2_0 r$2_0_old)
                (t$2_0 t$2_0_old)
                (x.0$2_0 x.0$2_0_old)
                (cmp$2_0 (< 0 c.addr.0$2_0)))
               (=>
                  cmp$2_0
                  (let
                     ((cmp3$2_0 (< 0 t$2_0))
                      (inc$2_0 (+ x.0$2_0 1)))
                     (let
                        ((inc.x.0$2_0 (ite cmp3$2_0 inc$2_0 x.0$2_0))
                         (dec$2_0 (+ c.addr.0$2_0 (- 1))))
                        (let
                           ((c.addr.0$2_0 dec$2_0)
                            (x.0$2_0 inc.x.0$2_0))
                           (INV_MAIN_23 r$1_0_old c.addr.0$2_0 r$2_0 t$2_0 x.0$2_0))))))))))
(assert
   (forall
      ((c.addr.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (c.addr.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_42 c.addr.0$1_0_old r$1_0_old x.0$1_0_old c.addr.0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((c.addr.0$1_0 c.addr.0$1_0_old))
            (let
               ((r$1_0 r$1_0_old)
                (x.0$1_0 x.0$1_0_old)
                (cmp1$1_0 (< 0 c.addr.0$1_0)))
               (=>
                  (not cmp1$1_0)
                  (let
                     ((r.addr.0$1_0 r$1_0)
                      (x.2$1_0 x.0$1_0)
                      (c.addr.0$2_0 c.addr.0$2_0_old))
                     (let
                        ((r$2_0 r$2_0_old)
                         (t$2_0 t$2_0_old)
                         (x.0$2_0 x.0$2_0_old)
                         (cmp$2_0 (< 0 c.addr.0$2_0)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((r.addr.0$2_0 r$2_0)
                               (x.2$2_0 x.0$2_0))
                              (INV_MAIN_13 r.addr.0$1_0 x.2$1_0 r.addr.0$2_0 x.2$2_0)))))))))))
(assert
   (forall
      ((c.addr.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (c.addr.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_42 c.addr.0$1_0_old r$1_0_old x.0$1_0_old c.addr.0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((c.addr.0$1_0 c.addr.0$1_0_old))
            (let
               ((r$1_0 r$1_0_old)
                (x.0$1_0 x.0$1_0_old)
                (cmp1$1_0 (< 0 c.addr.0$1_0)))
               (=>
                  cmp1$1_0
                  (let
                     ((inc$1_0 (+ x.0$1_0 1))
                      (dec$1_0 (+ c.addr.0$1_0 (- 1))))
                     (let
                        ((c.addr.0$1_0 dec$1_0)
                         (x.0$1_0 inc$1_0)
                         (c.addr.0$2_0 c.addr.0$2_0_old))
                        (let
                           ((r$2_0 r$2_0_old)
                            (t$2_0 t$2_0_old)
                            (x.0$2_0 x.0$2_0_old)
                            (cmp$2_0 (< 0 c.addr.0$2_0)))
                           (=>
                              cmp$2_0
                              (let
                                 ((cmp3$2_0 (< 0 t$2_0))
                                  (inc$2_0 (+ x.0$2_0 1)))
                                 (let
                                    ((inc.x.0$2_0 (ite cmp3$2_0 inc$2_0 x.0$2_0))
                                     (dec$2_0 (+ c.addr.0$2_0 (- 1))))
                                    (let
                                       ((c.addr.0$2_0 dec$2_0)
                                        (x.0$2_0 inc.x.0$2_0))
                                       (INV_MAIN_42 c.addr.0$1_0 r$1_0 x.0$1_0 c.addr.0$2_0 r$2_0 t$2_0 x.0$2_0))))))))))))))
(assert
   (forall
      ((c.addr.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (c.addr.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_42 c.addr.0$1_0_old r$1_0_old x.0$1_0_old c.addr.0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((c.addr.0$1_0 c.addr.0$1_0_old))
            (let
               ((r$1_0 r$1_0_old)
                (x.0$1_0 x.0$1_0_old)
                (cmp1$1_0 (< 0 c.addr.0$1_0)))
               (=>
                  cmp1$1_0
                  (let
                     ((inc$1_0 (+ x.0$1_0 1))
                      (dec$1_0 (+ c.addr.0$1_0 (- 1))))
                     (let
                        ((c.addr.0$1_0 dec$1_0)
                         (x.0$1_0 inc$1_0))
                        (=>
                           (let
                              ((c.addr.0$2_0 c.addr.0$2_0_old))
                              (let
                                 ((r$2_0 r$2_0_old)
                                  (t$2_0 t$2_0_old)
                                  (x.0$2_0 x.0$2_0_old)
                                  (cmp$2_0 (< 0 c.addr.0$2_0)))
                                 (=>
                                    cmp$2_0
                                    (let
                                       ((cmp3$2_0 (< 0 t$2_0))
                                        (inc$2_0 (+ x.0$2_0 1)))
                                       (let
                                          ((inc.x.0$2_0 (ite cmp3$2_0 inc$2_0 x.0$2_0))
                                           (dec$2_0 (+ c.addr.0$2_0 (- 1))))
                                          (let
                                             ((c.addr.0$2_0 dec$2_0)
                                              (x.0$2_0 inc.x.0$2_0))
                                             false))))))
                           (INV_MAIN_42 c.addr.0$1_0 r$1_0 x.0$1_0 c.addr.0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old))))))))))
(assert
   (forall
      ((c.addr.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (c.addr.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_42 c.addr.0$1_0_old r$1_0_old x.0$1_0_old c.addr.0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((c.addr.0$2_0 c.addr.0$2_0_old))
            (let
               ((r$2_0 r$2_0_old)
                (t$2_0 t$2_0_old)
                (x.0$2_0 x.0$2_0_old)
                (cmp$2_0 (< 0 c.addr.0$2_0)))
               (=>
                  cmp$2_0
                  (let
                     ((cmp3$2_0 (< 0 t$2_0))
                      (inc$2_0 (+ x.0$2_0 1)))
                     (let
                        ((inc.x.0$2_0 (ite cmp3$2_0 inc$2_0 x.0$2_0))
                         (dec$2_0 (+ c.addr.0$2_0 (- 1))))
                        (let
                           ((c.addr.0$2_0 dec$2_0)
                            (x.0$2_0 inc.x.0$2_0))
                           (=>
                              (let
                                 ((c.addr.0$1_0 c.addr.0$1_0_old))
                                 (let
                                    ((r$1_0 r$1_0_old)
                                     (x.0$1_0 x.0$1_0_old)
                                     (cmp1$1_0 (< 0 c.addr.0$1_0)))
                                    (=>
                                       cmp1$1_0
                                       (let
                                          ((inc$1_0 (+ x.0$1_0 1))
                                           (dec$1_0 (+ c.addr.0$1_0 (- 1))))
                                          (let
                                             ((c.addr.0$1_0 dec$1_0)
                                              (x.0$1_0 inc$1_0))
                                             false)))))
                              (INV_MAIN_42 c.addr.0$1_0_old r$1_0_old x.0$1_0_old c.addr.0$2_0 r$2_0 t$2_0 x.0$2_0)))))))))))
(check-sat)
(get-model)
