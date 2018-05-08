;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((s$1_0 Int)
    (c$1_0 Int)
    (n$1_0 Int)
    (HEAP$1 (Array Int Int))
    (s$2_0 Int)
    (c$2_0 Int)
    (n$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= s$1_0 s$2_0)
      (= c$1_0 c$2_0)
      (= n$1_0 n$2_0)
      (= HEAP$1 HEAP$2)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= result$1 result$2)
      (= HEAP$1 HEAP$2)))
; :annot (INV_MAIN_42 c$1_0 dec$1_0 pc.0$1_0 HEAP$1 c$2_0 incdec.ptr$2_0 n.addr.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_42
   (Int
    Int
    Int
    (Array Int Int)
    Int
    Int
    Int
    (Array Int Int))
   Bool)
(assert
   (forall
      ((s$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old c$1_0_old n$1_0_old HEAP$1_old s$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (n.addr.0$1_0 n$1_0))
               (let
                  ((pc.0$1_0 s$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 pc.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0))
                           (let
                              ((cmp$1_0 (= conv$1_0 c$1_0)))
                              (=>
                                 cmp$1_0
                                 (let
                                    ((retval.0$1_0 pc.0$1_0))
                                    (let
                                       ((result$1 retval.0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (s$2_0 s$2_0_old)
                                        (c$2_0 c$2_0_old)
                                        (n$2_0 n$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct n$2_0 0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((n.addr.0$2_0 n$2_0)
                                                 (p.0$2_0 s$2_0))
                                                (let
                                                   ((incdec.ptr$2_0 (+ p.0$2_0 1))
                                                    (_$2_0 (select HEAP$2 p.0$2_0)))
                                                   (let
                                                      ((conv$2_0 _$2_0)
                                                       (conv1$2_0 c$2_0))
                                                      (let
                                                         ((conv2$2_0 conv1$2_0))
                                                         (let
                                                            ((cmp3$2_0 (= conv$2_0 conv2$2_0)))
                                                            (not (not cmp3$2_0))))))))))))))))))))))
(assert
   (forall
      ((s$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old c$1_0_old n$1_0_old HEAP$1_old s$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (n.addr.0$1_0 n$1_0))
               (let
                  ((pc.0$1_0 s$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     (not tobool$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (s$2_0 s$2_0_old)
                            (c$2_0 c$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((HEAP$2 HEAP$2_old)
                               (cmp$2_0 (distinct n$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((n.addr.0$2_0 n$2_0)
                                     (p.0$2_0 s$2_0))
                                    (let
                                       ((incdec.ptr$2_0 (+ p.0$2_0 1))
                                        (_$2_0 (select HEAP$2 p.0$2_0)))
                                       (let
                                          ((conv$2_0 _$2_0)
                                           (conv1$2_0 c$2_0))
                                          (let
                                             ((conv2$2_0 conv1$2_0))
                                             (let
                                                ((cmp3$2_0 (= conv$2_0 conv2$2_0)))
                                                (not (not cmp3$2_0))))))))))))))))))
(assert
   (forall
      ((s$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old c$1_0_old n$1_0_old HEAP$1_old s$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (n.addr.0$1_0 n$1_0))
               (let
                  ((pc.0$1_0 s$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 pc.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0))
                           (let
                              ((cmp$1_0 (= conv$1_0 c$1_0)))
                              (=>
                                 (not cmp$1_0)
                                 (let
                                    ((s$2_0 s$2_0_old)
                                     (c$2_0 c$2_0_old)
                                     (n$2_0 n$2_0_old))
                                    (let
                                       ((HEAP$2 HEAP$2_old)
                                        (cmp$2_0 (distinct n$2_0 0)))
                                       (=>
                                          cmp$2_0
                                          (let
                                             ((n.addr.0$2_0 n$2_0)
                                              (p.0$2_0 s$2_0))
                                             (let
                                                ((incdec.ptr$2_0 (+ p.0$2_0 1))
                                                 (_$2_0 (select HEAP$2 p.0$2_0)))
                                                (let
                                                   ((conv$2_0 _$2_0)
                                                    (conv1$2_0 c$2_0))
                                                   (let
                                                      ((conv2$2_0 conv1$2_0))
                                                      (let
                                                         ((cmp3$2_0 (= conv$2_0 conv2$2_0)))
                                                         (=>
                                                            cmp3$2_0
                                                            (let
                                                               ((add.ptr$2_0 (+ incdec.ptr$2_0 (- 1))))
                                                               (let
                                                                  ((retval.0$2_0 add.ptr$2_0))
                                                                  (let
                                                                     ((result$2 retval.0$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     false)))))))))))))))))))))))
(assert
   (forall
      ((s$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old c$1_0_old n$1_0_old HEAP$1_old s$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (n.addr.0$1_0 n$1_0))
               (let
                  ((pc.0$1_0 s$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 pc.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0))
                           (let
                              ((cmp$1_0 (= conv$1_0 c$1_0)))
                              (=>
                                 (not cmp$1_0)
                                 (let
                                    ((s$2_0 s$2_0_old)
                                     (c$2_0 c$2_0_old)
                                     (n$2_0 n$2_0_old))
                                    (let
                                       ((HEAP$2 HEAP$2_old)
                                        (cmp$2_0 (distinct n$2_0 0)))
                                       (=>
                                          (not cmp$2_0)
                                          (let
                                             ((retval.0$2_0 0))
                                             (let
                                                ((result$2 retval.0$2_0)
                                                 (HEAP$2_res HEAP$2))
                                                false))))))))))))))))
(assert
   (forall
      ((s$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old c$1_0_old n$1_0_old HEAP$1_old s$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (n.addr.0$1_0 n$1_0))
               (let
                  ((pc.0$1_0 s$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 pc.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0))
                           (let
                              ((cmp$1_0 (= conv$1_0 c$1_0)))
                              (=>
                                 cmp$1_0
                                 (let
                                    ((retval.0$1_0 pc.0$1_0))
                                    (let
                                       ((result$1 retval.0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (s$2_0 s$2_0_old)
                                        (c$2_0 c$2_0_old)
                                        (n$2_0 n$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct n$2_0 0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((n.addr.0$2_0 n$2_0)
                                                 (p.0$2_0 s$2_0))
                                                (let
                                                   ((incdec.ptr$2_0 (+ p.0$2_0 1))
                                                    (_$2_0 (select HEAP$2 p.0$2_0)))
                                                   (let
                                                      ((conv$2_0 _$2_0)
                                                       (conv1$2_0 c$2_0))
                                                      (let
                                                         ((conv2$2_0 conv1$2_0))
                                                         (let
                                                            ((cmp3$2_0 (= conv$2_0 conv2$2_0)))
                                                            (=>
                                                               cmp3$2_0
                                                               (let
                                                                  ((add.ptr$2_0 (+ incdec.ptr$2_0 (- 1))))
                                                                  (let
                                                                     ((retval.0$2_0 add.ptr$2_0))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((s$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old c$1_0_old n$1_0_old HEAP$1_old s$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (n.addr.0$1_0 n$1_0))
               (let
                  ((pc.0$1_0 s$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 pc.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0))
                           (let
                              ((cmp$1_0 (= conv$1_0 c$1_0)))
                              (=>
                                 cmp$1_0
                                 (let
                                    ((retval.0$1_0 pc.0$1_0))
                                    (let
                                       ((result$1 retval.0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (s$2_0 s$2_0_old)
                                        (c$2_0 c$2_0_old)
                                        (n$2_0 n$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct n$2_0 0)))
                                          (=>
                                             (not cmp$2_0)
                                             (let
                                                ((retval.0$2_0 0))
                                                (let
                                                   ((result$2 retval.0$2_0)
                                                    (HEAP$2_res HEAP$2))
                                                   (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))
(assert
   (forall
      ((s$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old c$1_0_old n$1_0_old HEAP$1_old s$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (n.addr.0$1_0 n$1_0))
               (let
                  ((pc.0$1_0 s$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     (not tobool$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (s$2_0 s$2_0_old)
                            (c$2_0 c$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((HEAP$2 HEAP$2_old)
                               (cmp$2_0 (distinct n$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((n.addr.0$2_0 n$2_0)
                                     (p.0$2_0 s$2_0))
                                    (let
                                       ((incdec.ptr$2_0 (+ p.0$2_0 1))
                                        (_$2_0 (select HEAP$2 p.0$2_0)))
                                       (let
                                          ((conv$2_0 _$2_0)
                                           (conv1$2_0 c$2_0))
                                          (let
                                             ((conv2$2_0 conv1$2_0))
                                             (let
                                                ((cmp3$2_0 (= conv$2_0 conv2$2_0)))
                                                (=>
                                                   cmp3$2_0
                                                   (let
                                                      ((add.ptr$2_0 (+ incdec.ptr$2_0 (- 1))))
                                                      (let
                                                         ((retval.0$2_0 add.ptr$2_0))
                                                         (let
                                                            ((result$2 retval.0$2_0)
                                                             (HEAP$2_res HEAP$2))
                                                            (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))
(assert
   (forall
      ((s$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old c$1_0_old n$1_0_old HEAP$1_old s$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (n.addr.0$1_0 n$1_0))
               (let
                  ((pc.0$1_0 s$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     (not tobool$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (s$2_0 s$2_0_old)
                            (c$2_0 c$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((HEAP$2 HEAP$2_old)
                               (cmp$2_0 (distinct n$2_0 0)))
                              (=>
                                 (not cmp$2_0)
                                 (let
                                    ((retval.0$2_0 0))
                                    (let
                                       ((result$2 retval.0$2_0)
                                        (HEAP$2_res HEAP$2))
                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))
(assert
   (forall
      ((s$1_0_old Int)
       (c$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s$2_0_old Int)
       (c$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old c$1_0_old n$1_0_old HEAP$1_old s$2_0_old c$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old)
             (c$1_0 c$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (n.addr.0$1_0 n$1_0))
               (let
                  ((pc.0$1_0 s$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 pc.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0))
                           (let
                              ((cmp$1_0 (= conv$1_0 c$1_0)))
                              (=>
                                 (not cmp$1_0)
                                 (let
                                    ((s$2_0 s$2_0_old)
                                     (c$2_0 c$2_0_old)
                                     (n$2_0 n$2_0_old))
                                    (let
                                       ((HEAP$2 HEAP$2_old)
                                        (cmp$2_0 (distinct n$2_0 0)))
                                       (=>
                                          cmp$2_0
                                          (let
                                             ((n.addr.0$2_0 n$2_0)
                                              (p.0$2_0 s$2_0))
                                             (let
                                                ((incdec.ptr$2_0 (+ p.0$2_0 1))
                                                 (_$2_0 (select HEAP$2 p.0$2_0)))
                                                (let
                                                   ((conv$2_0 _$2_0)
                                                    (conv1$2_0 c$2_0))
                                                   (let
                                                      ((conv2$2_0 conv1$2_0))
                                                      (let
                                                         ((cmp3$2_0 (= conv$2_0 conv2$2_0)))
                                                         (=>
                                                            (not cmp3$2_0)
                                                            (INV_MAIN_42 c$1_0 dec$1_0 pc.0$1_0 HEAP$1 c$2_0 incdec.ptr$2_0 n.addr.0$2_0 HEAP$2)))))))))))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (dec$1_0_old Int)
       (pc.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (c$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c$1_0_old dec$1_0_old pc.0$1_0_old HEAP$1_old c$2_0_old incdec.ptr$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((c$1_0 c$1_0_old)
             (dec$1_0 dec$1_0_old)
             (pc.0$1_0 pc.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (incdec.ptr$1_0 (+ pc.0$1_0 1))
                (n.addr.0$1_0 dec$1_0))
               (let
                  ((pc.0$1_0 incdec.ptr$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 pc.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0))
                           (let
                              ((cmp$1_0 (= conv$1_0 c$1_0)))
                              (=>
                                 cmp$1_0
                                 (let
                                    ((retval.0$1_0 pc.0$1_0))
                                    (let
                                       ((result$1 retval.0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (c$2_0 c$2_0_old)
                                        (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                        (n.addr.0$2_0 n.addr.0$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (dec$2_0 (+ n.addr.0$2_0 (- 1))))
                                          (let
                                             ((cmp6$2_0 (distinct dec$2_0 0)))
                                             (=>
                                                cmp6$2_0
                                                (let
                                                   ((n.addr.0$2_0 dec$2_0)
                                                    (p.0$2_0 incdec.ptr$2_0))
                                                   (let
                                                      ((incdec.ptr$2_0 (+ p.0$2_0 1))
                                                       (_$2_0 (select HEAP$2 p.0$2_0)))
                                                      (let
                                                         ((conv$2_0 _$2_0)
                                                          (conv1$2_0 c$2_0))
                                                         (let
                                                            ((conv2$2_0 conv1$2_0))
                                                            (let
                                                               ((cmp3$2_0 (= conv$2_0 conv2$2_0)))
                                                               (=>
                                                                  cmp3$2_0
                                                                  (let
                                                                     ((add.ptr$2_0 (+ incdec.ptr$2_0 (- 1))))
                                                                     (let
                                                                        ((retval.0$2_0 add.ptr$2_0))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (dec$1_0_old Int)
       (pc.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (c$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c$1_0_old dec$1_0_old pc.0$1_0_old HEAP$1_old c$2_0_old incdec.ptr$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((c$1_0 c$1_0_old)
             (dec$1_0 dec$1_0_old)
             (pc.0$1_0 pc.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (incdec.ptr$1_0 (+ pc.0$1_0 1))
                (n.addr.0$1_0 dec$1_0))
               (let
                  ((pc.0$1_0 incdec.ptr$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 pc.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0))
                           (let
                              ((cmp$1_0 (= conv$1_0 c$1_0)))
                              (=>
                                 cmp$1_0
                                 (let
                                    ((retval.0$1_0 pc.0$1_0))
                                    (let
                                       ((result$1 retval.0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (c$2_0 c$2_0_old)
                                        (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                        (n.addr.0$2_0 n.addr.0$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (dec$2_0 (+ n.addr.0$2_0 (- 1))))
                                          (let
                                             ((cmp6$2_0 (distinct dec$2_0 0)))
                                             (=>
                                                (not cmp6$2_0)
                                                (let
                                                   ((retval.0$2_0 0))
                                                   (let
                                                      ((result$2 retval.0$2_0)
                                                       (HEAP$2_res HEAP$2))
                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (dec$1_0_old Int)
       (pc.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (c$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c$1_0_old dec$1_0_old pc.0$1_0_old HEAP$1_old c$2_0_old incdec.ptr$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((c$1_0 c$1_0_old)
             (dec$1_0 dec$1_0_old)
             (pc.0$1_0 pc.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (incdec.ptr$1_0 (+ pc.0$1_0 1))
                (n.addr.0$1_0 dec$1_0))
               (let
                  ((pc.0$1_0 incdec.ptr$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     (not tobool$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (c$2_0 c$2_0_old)
                            (incdec.ptr$2_0 incdec.ptr$2_0_old)
                            (n.addr.0$2_0 n.addr.0$2_0_old))
                           (let
                              ((HEAP$2 HEAP$2_old)
                               (dec$2_0 (+ n.addr.0$2_0 (- 1))))
                              (let
                                 ((cmp6$2_0 (distinct dec$2_0 0)))
                                 (=>
                                    cmp6$2_0
                                    (let
                                       ((n.addr.0$2_0 dec$2_0)
                                        (p.0$2_0 incdec.ptr$2_0))
                                       (let
                                          ((incdec.ptr$2_0 (+ p.0$2_0 1))
                                           (_$2_0 (select HEAP$2 p.0$2_0)))
                                          (let
                                             ((conv$2_0 _$2_0)
                                              (conv1$2_0 c$2_0))
                                             (let
                                                ((conv2$2_0 conv1$2_0))
                                                (let
                                                   ((cmp3$2_0 (= conv$2_0 conv2$2_0)))
                                                   (=>
                                                      cmp3$2_0
                                                      (let
                                                         ((add.ptr$2_0 (+ incdec.ptr$2_0 (- 1))))
                                                         (let
                                                            ((retval.0$2_0 add.ptr$2_0))
                                                            (let
                                                               ((result$2 retval.0$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (dec$1_0_old Int)
       (pc.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (c$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c$1_0_old dec$1_0_old pc.0$1_0_old HEAP$1_old c$2_0_old incdec.ptr$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((c$1_0 c$1_0_old)
             (dec$1_0 dec$1_0_old)
             (pc.0$1_0 pc.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (incdec.ptr$1_0 (+ pc.0$1_0 1))
                (n.addr.0$1_0 dec$1_0))
               (let
                  ((pc.0$1_0 incdec.ptr$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     (not tobool$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (c$2_0 c$2_0_old)
                            (incdec.ptr$2_0 incdec.ptr$2_0_old)
                            (n.addr.0$2_0 n.addr.0$2_0_old))
                           (let
                              ((HEAP$2 HEAP$2_old)
                               (dec$2_0 (+ n.addr.0$2_0 (- 1))))
                              (let
                                 ((cmp6$2_0 (distinct dec$2_0 0)))
                                 (=>
                                    (not cmp6$2_0)
                                    (let
                                       ((retval.0$2_0 0))
                                       (let
                                          ((result$2 retval.0$2_0)
                                           (HEAP$2_res HEAP$2))
                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (dec$1_0_old Int)
       (pc.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (c$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c$1_0_old dec$1_0_old pc.0$1_0_old HEAP$1_old c$2_0_old incdec.ptr$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((c$1_0 c$1_0_old)
             (dec$1_0 dec$1_0_old)
             (pc.0$1_0 pc.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (incdec.ptr$1_0 (+ pc.0$1_0 1))
                (n.addr.0$1_0 dec$1_0))
               (let
                  ((pc.0$1_0 incdec.ptr$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 pc.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0))
                           (let
                              ((cmp$1_0 (= conv$1_0 c$1_0)))
                              (=>
                                 (not cmp$1_0)
                                 (let
                                    ((c$2_0 c$2_0_old)
                                     (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                     (n.addr.0$2_0 n.addr.0$2_0_old))
                                    (let
                                       ((HEAP$2 HEAP$2_old)
                                        (dec$2_0 (+ n.addr.0$2_0 (- 1))))
                                       (let
                                          ((cmp6$2_0 (distinct dec$2_0 0)))
                                          (=>
                                             cmp6$2_0
                                             (let
                                                ((n.addr.0$2_0 dec$2_0)
                                                 (p.0$2_0 incdec.ptr$2_0))
                                                (let
                                                   ((incdec.ptr$2_0 (+ p.0$2_0 1))
                                                    (_$2_0 (select HEAP$2 p.0$2_0)))
                                                   (let
                                                      ((conv$2_0 _$2_0)
                                                       (conv1$2_0 c$2_0))
                                                      (let
                                                         ((conv2$2_0 conv1$2_0))
                                                         (let
                                                            ((cmp3$2_0 (= conv$2_0 conv2$2_0)))
                                                            (=>
                                                               (not cmp3$2_0)
                                                               (INV_MAIN_42 c$1_0 dec$1_0 pc.0$1_0 HEAP$1 c$2_0 incdec.ptr$2_0 n.addr.0$2_0 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (dec$1_0_old Int)
       (pc.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (c$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c$1_0_old dec$1_0_old pc.0$1_0_old HEAP$1_old c$2_0_old incdec.ptr$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((c$1_0 c$1_0_old)
             (dec$1_0 dec$1_0_old)
             (pc.0$1_0 pc.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (incdec.ptr$1_0 (+ pc.0$1_0 1))
                (n.addr.0$1_0 dec$1_0))
               (let
                  ((pc.0$1_0 incdec.ptr$1_0)
                   (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                   (tobool$1_0 (distinct n.addr.0$1_0 0)))
                  (=>
                     tobool$1_0
                     (let
                        ((_$1_0 (select HEAP$1 pc.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0))
                           (let
                              ((cmp$1_0 (= conv$1_0 c$1_0)))
                              (=>
                                 (not cmp$1_0)
                                 (=>
                                    (let
                                       ((c$2_0 c$2_0_old)
                                        (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                        (n.addr.0$2_0 n.addr.0$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (dec$2_0 (+ n.addr.0$2_0 (- 1))))
                                          (let
                                             ((cmp6$2_0 (distinct dec$2_0 0)))
                                             (=>
                                                cmp6$2_0
                                                (let
                                                   ((n.addr.0$2_0 dec$2_0)
                                                    (p.0$2_0 incdec.ptr$2_0))
                                                   (let
                                                      ((incdec.ptr$2_0 (+ p.0$2_0 1))
                                                       (_$2_0 (select HEAP$2 p.0$2_0)))
                                                      (let
                                                         ((conv$2_0 _$2_0)
                                                          (conv1$2_0 c$2_0))
                                                         (let
                                                            ((conv2$2_0 conv1$2_0))
                                                            (let
                                                               ((cmp3$2_0 (= conv$2_0 conv2$2_0)))
                                                               (not (not cmp3$2_0)))))))))))
                                    (INV_MAIN_42 c$1_0 dec$1_0 pc.0$1_0 HEAP$1 c$2_0_old incdec.ptr$2_0_old n.addr.0$2_0_old HEAP$2_old)))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (dec$1_0_old Int)
       (pc.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (c$2_0_old Int)
       (incdec.ptr$2_0_old Int)
       (n.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c$1_0_old dec$1_0_old pc.0$1_0_old HEAP$1_old c$2_0_old incdec.ptr$2_0_old n.addr.0$2_0_old HEAP$2_old)
         (let
            ((c$2_0 c$2_0_old)
             (incdec.ptr$2_0 incdec.ptr$2_0_old)
             (n.addr.0$2_0 n.addr.0$2_0_old))
            (let
               ((HEAP$2 HEAP$2_old)
                (dec$2_0 (+ n.addr.0$2_0 (- 1))))
               (let
                  ((cmp6$2_0 (distinct dec$2_0 0)))
                  (=>
                     cmp6$2_0
                     (let
                        ((n.addr.0$2_0 dec$2_0)
                         (p.0$2_0 incdec.ptr$2_0))
                        (let
                           ((incdec.ptr$2_0 (+ p.0$2_0 1))
                            (_$2_0 (select HEAP$2 p.0$2_0)))
                           (let
                              ((conv$2_0 _$2_0)
                               (conv1$2_0 c$2_0))
                              (let
                                 ((conv2$2_0 conv1$2_0))
                                 (let
                                    ((cmp3$2_0 (= conv$2_0 conv2$2_0)))
                                    (=>
                                       (not cmp3$2_0)
                                       (=>
                                          (let
                                             ((c$1_0 c$1_0_old)
                                              (dec$1_0 dec$1_0_old)
                                              (pc.0$1_0 pc.0$1_0_old))
                                             (let
                                                ((HEAP$1 HEAP$1_old)
                                                 (incdec.ptr$1_0 (+ pc.0$1_0 1))
                                                 (n.addr.0$1_0 dec$1_0))
                                                (let
                                                   ((pc.0$1_0 incdec.ptr$1_0)
                                                    (dec$1_0 (+ n.addr.0$1_0 (- 1)))
                                                    (tobool$1_0 (distinct n.addr.0$1_0 0)))
                                                   (=>
                                                      tobool$1_0
                                                      (let
                                                         ((_$1_0 (select HEAP$1 pc.0$1_0)))
                                                         (let
                                                            ((conv$1_0 _$1_0))
                                                            (let
                                                               ((cmp$1_0 (= conv$1_0 c$1_0)))
                                                               (not (not cmp$1_0)))))))))
                                          (INV_MAIN_42 c$1_0_old dec$1_0_old pc.0$1_0_old HEAP$1_old c$2_0 incdec.ptr$2_0 n.addr.0$2_0 HEAP$2)))))))))))))))
(check-sat)
(get-model)
