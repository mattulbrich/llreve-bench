;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((s1$1_0 Int)
    (s2$1_0 Int)
    (n$1_0 Int)
    (HEAP$1 (Array Int Int))
    (s1$2_0 Int)
    (s2$2_0 Int)
    (n$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= s1$1_0 s1$2_0)
      (= s2$1_0 s2$2_0)
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
; :annot (INV_MAIN_42 c1.0$1_0 c2.0$1_0 n.addr.0$1_0 s1.addr.0$1_0 s2.addr.0$1_0 HEAP$1 a.0$2_0 add.ptr$2_0 b.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_42
   (Int
    Int
    Int
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
      ((s1$1_0_old Int)
       (s2$1_0_old Int)
       (n$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s1$2_0_old Int)
       (s2$2_0_old Int)
       (n$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s1$1_0_old s2$1_0_old n$1_0_old HEAP$1_old s1$2_0_old s2$2_0_old n$2_0_old HEAP$2_old)
         (let
            ((s1$1_0 s1$1_0_old)
             (s2$1_0 s2$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (c2.0$1_0 0)
                (c1.0$1_0 0)
                (n.addr.0$1_0 n$1_0)
                (s2.addr.0$1_0 s2$1_0)
                (s1.addr.0$1_0 s1$1_0)
                (s1$2_0 s1$2_0_old)
                (s2$2_0 s2$2_0_old)
                (n$2_0 n$2_0_old))
               (let
                  ((HEAP$2 HEAP$2_old)
                   (add.ptr$2_0 (+ s1$2_0 n$2_0))
                   (a.0$2_0 s1$2_0)
                   (b.0$2_0 s2$2_0))
                  (INV_MAIN_42 c1.0$1_0 c2.0$1_0 n.addr.0$1_0 s1.addr.0$1_0 s2.addr.0$1_0 HEAP$1 a.0$2_0 add.ptr$2_0 b.0$2_0 HEAP$2)))))))
(assert
   (forall
      ((c1.0$1_0_old Int)
       (c2.0$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (s1.addr.0$1_0_old Int)
       (s2.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)
         (let
            ((c1.0$1_0 c1.0$1_0_old)
             (c2.0$1_0 c2.0$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((s1.addr.0$1_0 s1.addr.0$1_0_old)
                (s2.addr.0$1_0 s2.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (> (abs n.addr.0$1_0) (abs 0))))
               (=>
                  cmp$1_0
                  (let
                     ((incdec.ptr$1_0 (+ s1.addr.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.addr.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.addr.0$1_0))
                         (conv2$1_0 _$1_0))
                        (let
                           ((cmp3$1_0 (= conv2$1_0 0)))
                           (=>
                              cmp3$1_0
                              (let
                                 ((c1.0.sink$1_0 _$1_0)
                                  (c2.0.sink$1_0 _$1_1))
                                 (let
                                    ((conv11$1_0 c1.0.sink$1_0)
                                     (conv12$1_0 c2.0.sink$1_0))
                                    (let
                                       ((sub13$1_0 (- conv11$1_0 conv12$1_0)))
                                       (let
                                          ((result$1 sub13$1_0)
                                           (HEAP$1_res HEAP$1)
                                           (a.0$2_0 a.0$2_0_old)
                                           (add.ptr$2_0 add.ptr$2_0_old))
                                          (let
                                             ((b.0$2_0 b.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                             (=>
                                                cmp$2_0
                                                (let
                                                   ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                   (let
                                                      ((conv1$2_0 _$2_0)
                                                       (_$2_1 (select HEAP$2 b.0$2_0)))
                                                      (let
                                                         ((conv2$2_0 _$2_1))
                                                         (let
                                                            ((sub$2_0 (- conv1$2_0 conv2$2_0)))
                                                            (let
                                                               ((tobool3$2_0 (distinct sub$2_0 0)))
                                                               (=>
                                                                  tobool3$2_0
                                                                  (let
                                                                     ((retval.0$2_0 sub$2_0))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((c1.0$1_0_old Int)
       (c2.0$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (s1.addr.0$1_0_old Int)
       (s2.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)
         (let
            ((c1.0$1_0 c1.0$1_0_old)
             (c2.0$1_0 c2.0$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((s1.addr.0$1_0 s1.addr.0$1_0_old)
                (s2.addr.0$1_0 s2.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (> (abs n.addr.0$1_0) (abs 0))))
               (=>
                  cmp$1_0
                  (let
                     ((incdec.ptr$1_0 (+ s1.addr.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.addr.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.addr.0$1_0))
                         (conv2$1_0 _$1_0))
                        (let
                           ((cmp3$1_0 (= conv2$1_0 0)))
                           (=>
                              cmp3$1_0
                              (let
                                 ((c1.0.sink$1_0 _$1_0)
                                  (c2.0.sink$1_0 _$1_1))
                                 (let
                                    ((conv11$1_0 c1.0.sink$1_0)
                                     (conv12$1_0 c2.0.sink$1_0))
                                    (let
                                       ((sub13$1_0 (- conv11$1_0 conv12$1_0)))
                                       (let
                                          ((result$1 sub13$1_0)
                                           (HEAP$1_res HEAP$1)
                                           (a.0$2_0 a.0$2_0_old)
                                           (add.ptr$2_0 add.ptr$2_0_old))
                                          (let
                                             ((b.0$2_0 b.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                             (=>
                                                cmp$2_0
                                                (let
                                                   ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                   (let
                                                      ((conv1$2_0 _$2_0)
                                                       (_$2_1 (select HEAP$2 b.0$2_0)))
                                                      (let
                                                         ((conv2$2_0 _$2_1))
                                                         (let
                                                            ((sub$2_0 (- conv1$2_0 conv2$2_0)))
                                                            (let
                                                               ((tobool3$2_0 (distinct sub$2_0 0)))
                                                               (=>
                                                                  (not tobool3$2_0)
                                                                  (let
                                                                     ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                     (let
                                                                        ((tobool4$2_0 (distinct _$2_2 0)))
                                                                        (=>
                                                                           (not tobool4$2_0)
                                                                           (let
                                                                              ((retval.0$2_0 0))
                                                                              (let
                                                                                 ((result$2 retval.0$2_0)
                                                                                  (HEAP$2_res HEAP$2))
                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))
(assert
   (forall
      ((c1.0$1_0_old Int)
       (c2.0$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (s1.addr.0$1_0_old Int)
       (s2.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)
         (let
            ((c1.0$1_0 c1.0$1_0_old)
             (c2.0$1_0 c2.0$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((s1.addr.0$1_0 s1.addr.0$1_0_old)
                (s2.addr.0$1_0 s2.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (> (abs n.addr.0$1_0) (abs 0))))
               (=>
                  cmp$1_0
                  (let
                     ((incdec.ptr$1_0 (+ s1.addr.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.addr.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.addr.0$1_0))
                         (conv2$1_0 _$1_0))
                        (let
                           ((cmp3$1_0 (= conv2$1_0 0)))
                           (=>
                              cmp3$1_0
                              (let
                                 ((c1.0.sink$1_0 _$1_0)
                                  (c2.0.sink$1_0 _$1_1))
                                 (let
                                    ((conv11$1_0 c1.0.sink$1_0)
                                     (conv12$1_0 c2.0.sink$1_0))
                                    (let
                                       ((sub13$1_0 (- conv11$1_0 conv12$1_0)))
                                       (let
                                          ((result$1 sub13$1_0)
                                           (HEAP$1_res HEAP$1)
                                           (a.0$2_0 a.0$2_0_old)
                                           (add.ptr$2_0 add.ptr$2_0_old))
                                          (let
                                             ((b.0$2_0 b.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                             (=>
                                                (not cmp$2_0)
                                                (let
                                                   ((retval.0$2_0 0))
                                                   (let
                                                      ((result$2 retval.0$2_0)
                                                       (HEAP$2_res HEAP$2))
                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))
(assert
   (forall
      ((c1.0$1_0_old Int)
       (c2.0$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (s1.addr.0$1_0_old Int)
       (s2.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)
         (let
            ((c1.0$1_0 c1.0$1_0_old)
             (c2.0$1_0 c2.0$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((s1.addr.0$1_0 s1.addr.0$1_0_old)
                (s2.addr.0$1_0 s2.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (> (abs n.addr.0$1_0) (abs 0))))
               (=>
                  cmp$1_0
                  (let
                     ((incdec.ptr$1_0 (+ s1.addr.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.addr.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.addr.0$1_0))
                         (conv2$1_0 _$1_0))
                        (let
                           ((cmp3$1_0 (= conv2$1_0 0)))
                           (=>
                              (not cmp3$1_0)
                              (let
                                 ((conv5$1_0 _$1_0)
                                  (conv6$1_0 _$1_1))
                                 (let
                                    ((cmp7$1_0 (distinct conv5$1_0 conv6$1_0)))
                                    (=>
                                       cmp7$1_0
                                       (let
                                          ((c1.0.sink$1_0 _$1_0)
                                           (c2.0.sink$1_0 _$1_1))
                                          (let
                                             ((conv11$1_0 c1.0.sink$1_0)
                                              (conv12$1_0 c2.0.sink$1_0))
                                             (let
                                                ((sub13$1_0 (- conv11$1_0 conv12$1_0)))
                                                (let
                                                   ((result$1 sub13$1_0)
                                                    (HEAP$1_res HEAP$1)
                                                    (a.0$2_0 a.0$2_0_old)
                                                    (add.ptr$2_0 add.ptr$2_0_old))
                                                   (let
                                                      ((b.0$2_0 b.0$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                            (let
                                                               ((conv1$2_0 _$2_0)
                                                                (_$2_1 (select HEAP$2 b.0$2_0)))
                                                               (let
                                                                  ((conv2$2_0 _$2_1))
                                                                  (let
                                                                     ((sub$2_0 (- conv1$2_0 conv2$2_0)))
                                                                     (let
                                                                        ((tobool3$2_0 (distinct sub$2_0 0)))
                                                                        (=>
                                                                           tobool3$2_0
                                                                           (let
                                                                              ((retval.0$2_0 sub$2_0))
                                                                              (let
                                                                                 ((result$2 retval.0$2_0)
                                                                                  (HEAP$2_res HEAP$2))
                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))
(assert
   (forall
      ((c1.0$1_0_old Int)
       (c2.0$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (s1.addr.0$1_0_old Int)
       (s2.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)
         (let
            ((c1.0$1_0 c1.0$1_0_old)
             (c2.0$1_0 c2.0$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((s1.addr.0$1_0 s1.addr.0$1_0_old)
                (s2.addr.0$1_0 s2.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (> (abs n.addr.0$1_0) (abs 0))))
               (=>
                  cmp$1_0
                  (let
                     ((incdec.ptr$1_0 (+ s1.addr.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.addr.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.addr.0$1_0))
                         (conv2$1_0 _$1_0))
                        (let
                           ((cmp3$1_0 (= conv2$1_0 0)))
                           (=>
                              (not cmp3$1_0)
                              (let
                                 ((conv5$1_0 _$1_0)
                                  (conv6$1_0 _$1_1))
                                 (let
                                    ((cmp7$1_0 (distinct conv5$1_0 conv6$1_0)))
                                    (=>
                                       cmp7$1_0
                                       (let
                                          ((c1.0.sink$1_0 _$1_0)
                                           (c2.0.sink$1_0 _$1_1))
                                          (let
                                             ((conv11$1_0 c1.0.sink$1_0)
                                              (conv12$1_0 c2.0.sink$1_0))
                                             (let
                                                ((sub13$1_0 (- conv11$1_0 conv12$1_0)))
                                                (let
                                                   ((result$1 sub13$1_0)
                                                    (HEAP$1_res HEAP$1)
                                                    (a.0$2_0 a.0$2_0_old)
                                                    (add.ptr$2_0 add.ptr$2_0_old))
                                                   (let
                                                      ((b.0$2_0 b.0$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                            (let
                                                               ((conv1$2_0 _$2_0)
                                                                (_$2_1 (select HEAP$2 b.0$2_0)))
                                                               (let
                                                                  ((conv2$2_0 _$2_1))
                                                                  (let
                                                                     ((sub$2_0 (- conv1$2_0 conv2$2_0)))
                                                                     (let
                                                                        ((tobool3$2_0 (distinct sub$2_0 0)))
                                                                        (=>
                                                                           (not tobool3$2_0)
                                                                           (let
                                                                              ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                              (let
                                                                                 ((tobool4$2_0 (distinct _$2_2 0)))
                                                                                 (=>
                                                                                    (not tobool4$2_0)
                                                                                    (let
                                                                                       ((retval.0$2_0 0))
                                                                                       (let
                                                                                          ((result$2 retval.0$2_0)
                                                                                           (HEAP$2_res HEAP$2))
                                                                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))
(assert
   (forall
      ((c1.0$1_0_old Int)
       (c2.0$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (s1.addr.0$1_0_old Int)
       (s2.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)
         (let
            ((c1.0$1_0 c1.0$1_0_old)
             (c2.0$1_0 c2.0$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((s1.addr.0$1_0 s1.addr.0$1_0_old)
                (s2.addr.0$1_0 s2.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (> (abs n.addr.0$1_0) (abs 0))))
               (=>
                  cmp$1_0
                  (let
                     ((incdec.ptr$1_0 (+ s1.addr.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.addr.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.addr.0$1_0))
                         (conv2$1_0 _$1_0))
                        (let
                           ((cmp3$1_0 (= conv2$1_0 0)))
                           (=>
                              (not cmp3$1_0)
                              (let
                                 ((conv5$1_0 _$1_0)
                                  (conv6$1_0 _$1_1))
                                 (let
                                    ((cmp7$1_0 (distinct conv5$1_0 conv6$1_0)))
                                    (=>
                                       cmp7$1_0
                                       (let
                                          ((c1.0.sink$1_0 _$1_0)
                                           (c2.0.sink$1_0 _$1_1))
                                          (let
                                             ((conv11$1_0 c1.0.sink$1_0)
                                              (conv12$1_0 c2.0.sink$1_0))
                                             (let
                                                ((sub13$1_0 (- conv11$1_0 conv12$1_0)))
                                                (let
                                                   ((result$1 sub13$1_0)
                                                    (HEAP$1_res HEAP$1)
                                                    (a.0$2_0 a.0$2_0_old)
                                                    (add.ptr$2_0 add.ptr$2_0_old))
                                                   (let
                                                      ((b.0$2_0 b.0$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                      (=>
                                                         (not cmp$2_0)
                                                         (let
                                                            ((retval.0$2_0 0))
                                                            (let
                                                               ((result$2 retval.0$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((c1.0$1_0_old Int)
       (c2.0$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (s1.addr.0$1_0_old Int)
       (s2.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)
         (let
            ((c1.0$1_0 c1.0$1_0_old)
             (c2.0$1_0 c2.0$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((s1.addr.0$1_0 s1.addr.0$1_0_old)
                (s2.addr.0$1_0 s2.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (> (abs n.addr.0$1_0) (abs 0))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((c1.0.sink$1_0 c1.0$1_0)
                      (c2.0.sink$1_0 c2.0$1_0))
                     (let
                        ((conv11$1_0 c1.0.sink$1_0)
                         (conv12$1_0 c2.0.sink$1_0))
                        (let
                           ((sub13$1_0 (- conv11$1_0 conv12$1_0)))
                           (let
                              ((result$1 sub13$1_0)
                               (HEAP$1_res HEAP$1)
                               (a.0$2_0 a.0$2_0_old)
                               (add.ptr$2_0 add.ptr$2_0_old))
                              (let
                                 ((b.0$2_0 b.0$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                 (=>
                                    cmp$2_0
                                    (let
                                       ((_$2_0 (select HEAP$2 a.0$2_0)))
                                       (let
                                          ((conv1$2_0 _$2_0)
                                           (_$2_1 (select HEAP$2 b.0$2_0)))
                                          (let
                                             ((conv2$2_0 _$2_1))
                                             (let
                                                ((sub$2_0 (- conv1$2_0 conv2$2_0)))
                                                (let
                                                   ((tobool3$2_0 (distinct sub$2_0 0)))
                                                   (=>
                                                      tobool3$2_0
                                                      (let
                                                         ((retval.0$2_0 sub$2_0))
                                                         (let
                                                            ((result$2 retval.0$2_0)
                                                             (HEAP$2_res HEAP$2))
                                                            (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))
(assert
   (forall
      ((c1.0$1_0_old Int)
       (c2.0$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (s1.addr.0$1_0_old Int)
       (s2.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)
         (let
            ((c1.0$1_0 c1.0$1_0_old)
             (c2.0$1_0 c2.0$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((s1.addr.0$1_0 s1.addr.0$1_0_old)
                (s2.addr.0$1_0 s2.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (> (abs n.addr.0$1_0) (abs 0))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((c1.0.sink$1_0 c1.0$1_0)
                      (c2.0.sink$1_0 c2.0$1_0))
                     (let
                        ((conv11$1_0 c1.0.sink$1_0)
                         (conv12$1_0 c2.0.sink$1_0))
                        (let
                           ((sub13$1_0 (- conv11$1_0 conv12$1_0)))
                           (let
                              ((result$1 sub13$1_0)
                               (HEAP$1_res HEAP$1)
                               (a.0$2_0 a.0$2_0_old)
                               (add.ptr$2_0 add.ptr$2_0_old))
                              (let
                                 ((b.0$2_0 b.0$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                 (=>
                                    cmp$2_0
                                    (let
                                       ((_$2_0 (select HEAP$2 a.0$2_0)))
                                       (let
                                          ((conv1$2_0 _$2_0)
                                           (_$2_1 (select HEAP$2 b.0$2_0)))
                                          (let
                                             ((conv2$2_0 _$2_1))
                                             (let
                                                ((sub$2_0 (- conv1$2_0 conv2$2_0)))
                                                (let
                                                   ((tobool3$2_0 (distinct sub$2_0 0)))
                                                   (=>
                                                      (not tobool3$2_0)
                                                      (let
                                                         ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                         (let
                                                            ((tobool4$2_0 (distinct _$2_2 0)))
                                                            (=>
                                                               (not tobool4$2_0)
                                                               (let
                                                                  ((retval.0$2_0 0))
                                                                  (let
                                                                     ((result$2 retval.0$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))
(assert
   (forall
      ((c1.0$1_0_old Int)
       (c2.0$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (s1.addr.0$1_0_old Int)
       (s2.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)
         (let
            ((c1.0$1_0 c1.0$1_0_old)
             (c2.0$1_0 c2.0$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((s1.addr.0$1_0 s1.addr.0$1_0_old)
                (s2.addr.0$1_0 s2.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (> (abs n.addr.0$1_0) (abs 0))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((c1.0.sink$1_0 c1.0$1_0)
                      (c2.0.sink$1_0 c2.0$1_0))
                     (let
                        ((conv11$1_0 c1.0.sink$1_0)
                         (conv12$1_0 c2.0.sink$1_0))
                        (let
                           ((sub13$1_0 (- conv11$1_0 conv12$1_0)))
                           (let
                              ((result$1 sub13$1_0)
                               (HEAP$1_res HEAP$1)
                               (a.0$2_0 a.0$2_0_old)
                               (add.ptr$2_0 add.ptr$2_0_old))
                              (let
                                 ((b.0$2_0 b.0$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                 (=>
                                    (not cmp$2_0)
                                    (let
                                       ((retval.0$2_0 0))
                                       (let
                                          ((result$2 retval.0$2_0)
                                           (HEAP$2_res HEAP$2))
                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))
(assert
   (forall
      ((c1.0$1_0_old Int)
       (c2.0$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (s1.addr.0$1_0_old Int)
       (s2.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)
         (let
            ((c1.0$1_0 c1.0$1_0_old)
             (c2.0$1_0 c2.0$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((s1.addr.0$1_0 s1.addr.0$1_0_old)
                (s2.addr.0$1_0 s2.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (> (abs n.addr.0$1_0) (abs 0))))
               (=>
                  cmp$1_0
                  (let
                     ((incdec.ptr$1_0 (+ s1.addr.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.addr.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.addr.0$1_0))
                         (conv2$1_0 _$1_0))
                        (let
                           ((cmp3$1_0 (= conv2$1_0 0)))
                           (=>
                              (not cmp3$1_0)
                              (let
                                 ((conv5$1_0 _$1_0)
                                  (conv6$1_0 _$1_1))
                                 (let
                                    ((cmp7$1_0 (distinct conv5$1_0 conv6$1_0)))
                                    (=>
                                       (not cmp7$1_0)
                                       (let
                                          ((dec$1_0 (+ n.addr.0$1_0 (- 1))))
                                          (let
                                             ((c2.0$1_0 _$1_1)
                                              (c1.0$1_0 _$1_0)
                                              (n.addr.0$1_0 dec$1_0)
                                              (s2.addr.0$1_0 incdec.ptr1$1_0)
                                              (s1.addr.0$1_0 incdec.ptr$1_0)
                                              (a.0$2_0 a.0$2_0_old)
                                              (add.ptr$2_0 add.ptr$2_0_old))
                                             (let
                                                ((b.0$2_0 b.0$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                (=>
                                                   cmp$2_0
                                                   (let
                                                      ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                      (let
                                                         ((conv1$2_0 _$2_0)
                                                          (_$2_1 (select HEAP$2 b.0$2_0)))
                                                         (let
                                                            ((conv2$2_0 _$2_1))
                                                            (let
                                                               ((sub$2_0 (- conv1$2_0 conv2$2_0)))
                                                               (let
                                                                  ((tobool3$2_0 (distinct sub$2_0 0)))
                                                                  (=>
                                                                     (not tobool3$2_0)
                                                                     (let
                                                                        ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                        (let
                                                                           ((tobool4$2_0 (distinct _$2_2 0)))
                                                                           (=>
                                                                              tobool4$2_0
                                                                              (let
                                                                                 ((incdec.ptr$2_0 (+ a.0$2_0 1))
                                                                                  (incdec.ptr7$2_0 (+ b.0$2_0 1)))
                                                                                 (let
                                                                                    ((a.0$2_0 incdec.ptr$2_0)
                                                                                     (b.0$2_0 incdec.ptr7$2_0))
                                                                                    (INV_MAIN_42 c1.0$1_0 c2.0$1_0 n.addr.0$1_0 s1.addr.0$1_0 s2.addr.0$1_0 HEAP$1 a.0$2_0 add.ptr$2_0 b.0$2_0 HEAP$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((c1.0$1_0_old Int)
       (c2.0$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (s1.addr.0$1_0_old Int)
       (s2.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)
         (let
            ((c1.0$1_0 c1.0$1_0_old)
             (c2.0$1_0 c2.0$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((s1.addr.0$1_0 s1.addr.0$1_0_old)
                (s2.addr.0$1_0 s2.addr.0$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (> (abs n.addr.0$1_0) (abs 0))))
               (=>
                  cmp$1_0
                  (let
                     ((incdec.ptr$1_0 (+ s1.addr.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.addr.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.addr.0$1_0))
                         (conv2$1_0 _$1_0))
                        (let
                           ((cmp3$1_0 (= conv2$1_0 0)))
                           (=>
                              (not cmp3$1_0)
                              (let
                                 ((conv5$1_0 _$1_0)
                                  (conv6$1_0 _$1_1))
                                 (let
                                    ((cmp7$1_0 (distinct conv5$1_0 conv6$1_0)))
                                    (=>
                                       (not cmp7$1_0)
                                       (let
                                          ((dec$1_0 (+ n.addr.0$1_0 (- 1))))
                                          (let
                                             ((c2.0$1_0 _$1_1)
                                              (c1.0$1_0 _$1_0)
                                              (n.addr.0$1_0 dec$1_0)
                                              (s2.addr.0$1_0 incdec.ptr1$1_0)
                                              (s1.addr.0$1_0 incdec.ptr$1_0))
                                             (=>
                                                (let
                                                   ((a.0$2_0 a.0$2_0_old)
                                                    (add.ptr$2_0 add.ptr$2_0_old))
                                                   (let
                                                      ((b.0$2_0 b.0$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                            (let
                                                               ((conv1$2_0 _$2_0)
                                                                (_$2_1 (select HEAP$2 b.0$2_0)))
                                                               (let
                                                                  ((conv2$2_0 _$2_1))
                                                                  (let
                                                                     ((sub$2_0 (- conv1$2_0 conv2$2_0)))
                                                                     (let
                                                                        ((tobool3$2_0 (distinct sub$2_0 0)))
                                                                        (=>
                                                                           (not tobool3$2_0)
                                                                           (let
                                                                              ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                              (let
                                                                                 ((tobool4$2_0 (distinct _$2_2 0)))
                                                                                 (=>
                                                                                    tobool4$2_0
                                                                                    (let
                                                                                       ((incdec.ptr$2_0 (+ a.0$2_0 1))
                                                                                        (incdec.ptr7$2_0 (+ b.0$2_0 1)))
                                                                                       (let
                                                                                          ((a.0$2_0 incdec.ptr$2_0)
                                                                                           (b.0$2_0 incdec.ptr7$2_0))
                                                                                          false))))))))))))))
                                                (INV_MAIN_42 c1.0$1_0 c2.0$1_0 n.addr.0$1_0 s1.addr.0$1_0 s2.addr.0$1_0 HEAP$1 a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)))))))))))))))))
(assert
   (forall
      ((c1.0$1_0_old Int)
       (c2.0$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (s1.addr.0$1_0_old Int)
       (s2.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0_old add.ptr$2_0_old b.0$2_0_old HEAP$2_old)
         (let
            ((a.0$2_0 a.0$2_0_old)
             (add.ptr$2_0 add.ptr$2_0_old))
            (let
               ((b.0$2_0 b.0$2_0_old)
                (HEAP$2 HEAP$2_old)
                (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
               (=>
                  cmp$2_0
                  (let
                     ((_$2_0 (select HEAP$2 a.0$2_0)))
                     (let
                        ((conv1$2_0 _$2_0)
                         (_$2_1 (select HEAP$2 b.0$2_0)))
                        (let
                           ((conv2$2_0 _$2_1))
                           (let
                              ((sub$2_0 (- conv1$2_0 conv2$2_0)))
                              (let
                                 ((tobool3$2_0 (distinct sub$2_0 0)))
                                 (=>
                                    (not tobool3$2_0)
                                    (let
                                       ((_$2_2 (select HEAP$2 a.0$2_0)))
                                       (let
                                          ((tobool4$2_0 (distinct _$2_2 0)))
                                          (=>
                                             tobool4$2_0
                                             (let
                                                ((incdec.ptr$2_0 (+ a.0$2_0 1))
                                                 (incdec.ptr7$2_0 (+ b.0$2_0 1)))
                                                (let
                                                   ((a.0$2_0 incdec.ptr$2_0)
                                                    (b.0$2_0 incdec.ptr7$2_0))
                                                   (=>
                                                      (let
                                                         ((c1.0$1_0 c1.0$1_0_old)
                                                          (c2.0$1_0 c2.0$1_0_old)
                                                          (n.addr.0$1_0 n.addr.0$1_0_old))
                                                         (let
                                                            ((s1.addr.0$1_0 s1.addr.0$1_0_old)
                                                             (s2.addr.0$1_0 s2.addr.0$1_0_old)
                                                             (HEAP$1 HEAP$1_old)
                                                             (cmp$1_0 (> (abs n.addr.0$1_0) (abs 0))))
                                                            (=>
                                                               cmp$1_0
                                                               (let
                                                                  ((incdec.ptr$1_0 (+ s1.addr.0$1_0 1))
                                                                   (_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                                                                  (let
                                                                     ((incdec.ptr1$1_0 (+ s2.addr.0$1_0 1))
                                                                      (_$1_1 (select HEAP$1 s2.addr.0$1_0))
                                                                      (conv2$1_0 _$1_0))
                                                                     (let
                                                                        ((cmp3$1_0 (= conv2$1_0 0)))
                                                                        (=>
                                                                           (not cmp3$1_0)
                                                                           (let
                                                                              ((conv5$1_0 _$1_0)
                                                                               (conv6$1_0 _$1_1))
                                                                              (let
                                                                                 ((cmp7$1_0 (distinct conv5$1_0 conv6$1_0)))
                                                                                 (=>
                                                                                    (not cmp7$1_0)
                                                                                    (let
                                                                                       ((dec$1_0 (+ n.addr.0$1_0 (- 1))))
                                                                                       (let
                                                                                          ((c2.0$1_0 _$1_1)
                                                                                           (c1.0$1_0 _$1_0)
                                                                                           (n.addr.0$1_0 dec$1_0)
                                                                                           (s2.addr.0$1_0 incdec.ptr1$1_0)
                                                                                           (s1.addr.0$1_0 incdec.ptr$1_0))
                                                                                          false))))))))))))
                                                      (INV_MAIN_42 c1.0$1_0_old c2.0$1_0_old n.addr.0$1_0_old s1.addr.0$1_0_old s2.addr.0$1_0_old HEAP$1_old a.0$2_0 add.ptr$2_0 b.0$2_0 HEAP$2)))))))))))))))))))
(check-sat)
(get-model)
