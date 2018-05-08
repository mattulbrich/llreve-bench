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
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= result$1 result$2)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))))
; :annot (INV_MAIN_42 incdec.ptr$1_0 incdec.ptr9$1_0 n.addr.0$1_0 HEAP$1 a.0$2_0 add.ptr$2_0 b.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_42
   (Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int)
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((retval.0$1_0 0))
                     (let
                        ((result$1 retval.0$1_0)
                         (HEAP$1_res HEAP$1)
                         (s1$2_0 s1$2_0_old)
                         (s2$2_0 s2$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (add.ptr$2_0 (+ s1$2_0 n$2_0))
                            (a.0$2_0 s1$2_0))
                           (let
                              ((b.0$2_0 s2$2_0)
                               (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((_$2_0 (select HEAP$2 a.0$2_0)))
                                    (let
                                       ((conv$2_0 _$2_0)
                                        (_$2_1 (select HEAP$2 b.0$2_0)))
                                       (let
                                          ((conv1$2_0 _$2_1))
                                          (let
                                             ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                             (let
                                                ((tobool$2_0 (distinct sub$2_0 0)))
                                                (=>
                                                   (not tobool$2_0)
                                                   (let
                                                      ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                      (let
                                                         ((tobool2$2_0 (distinct _$2_2 0)))
                                                         (not tobool2$2_0))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (s2.addr.0$1_0 s2$1_0)
                      (s1.addr.0$1_0 s1$1_0))
                     (let
                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0)
                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                 (=>
                                    cmp2$1_0
                                    (let
                                       ((_$1_2 (select HEAP$1 s1.addr.0$1_0)))
                                       (let
                                          ((conv5$1_0 _$1_2)
                                           (incdec.ptr6$1_0 (+ incdec.ptr$1_0 (- 1))))
                                          (let
                                             ((_$1_3 (select HEAP$1 incdec.ptr6$1_0)))
                                             (let
                                                ((conv7$1_0 _$1_3))
                                                (let
                                                   ((sub$1_0 (- conv5$1_0 conv7$1_0)))
                                                   (let
                                                      ((retval.0$1_0 sub$1_0))
                                                      (let
                                                         ((result$1 retval.0$1_0)
                                                          (HEAP$1_res HEAP$1)
                                                          (s1$2_0 s1$2_0_old)
                                                          (s2$2_0 s2$2_0_old)
                                                          (n$2_0 n$2_0_old))
                                                         (let
                                                            ((HEAP$2 HEAP$2_old)
                                                             (add.ptr$2_0 (+ s1$2_0 n$2_0))
                                                             (a.0$2_0 s1$2_0))
                                                            (let
                                                               ((b.0$2_0 s2$2_0)
                                                                (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                               (=>
                                                                  cmp$2_0
                                                                  (let
                                                                     ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                                     (let
                                                                        ((conv$2_0 _$2_0)
                                                                         (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                        (let
                                                                           ((conv1$2_0 _$2_1))
                                                                           (let
                                                                              ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                              (let
                                                                                 ((tobool$2_0 (distinct sub$2_0 0)))
                                                                                 (=>
                                                                                    (not tobool$2_0)
                                                                                    (let
                                                                                       ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                                       (let
                                                                                          ((tobool2$2_0 (distinct _$2_2 0)))
                                                                                          (not tobool2$2_0)))))))))))))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (s2.addr.0$1_0 s2$1_0)
                      (s1.addr.0$1_0 s1$1_0))
                     (let
                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0)
                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                        (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                       (let
                                          ((conv10$1_0 _$1_4))
                                          (let
                                             ((cmp11$1_0 (= conv10$1_0 0)))
                                             (=>
                                                cmp11$1_0
                                                (let
                                                   ((retval.0$1_0 0))
                                                   (let
                                                      ((result$1 retval.0$1_0)
                                                       (HEAP$1_res HEAP$1)
                                                       (s1$2_0 s1$2_0_old)
                                                       (s2$2_0 s2$2_0_old)
                                                       (n$2_0 n$2_0_old))
                                                      (let
                                                         ((HEAP$2 HEAP$2_old)
                                                          (add.ptr$2_0 (+ s1$2_0 n$2_0))
                                                          (a.0$2_0 s1$2_0))
                                                         (let
                                                            ((b.0$2_0 s2$2_0)
                                                             (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                            (=>
                                                               cmp$2_0
                                                               (let
                                                                  ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                                  (let
                                                                     ((conv$2_0 _$2_0)
                                                                      (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                     (let
                                                                        ((conv1$2_0 _$2_1))
                                                                        (let
                                                                           ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                           (let
                                                                              ((tobool$2_0 (distinct sub$2_0 0)))
                                                                              (=>
                                                                                 (not tobool$2_0)
                                                                                 (let
                                                                                    ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                                    (let
                                                                                       ((tobool2$2_0 (distinct _$2_2 0)))
                                                                                       (not tobool2$2_0))))))))))))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (s2.addr.0$1_0 s2$1_0)
                      (s1.addr.0$1_0 s1$1_0))
                     (let
                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0)
                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                        (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                       (let
                                          ((conv10$1_0 _$1_4))
                                          (let
                                             ((cmp11$1_0 (= conv10$1_0 0)))
                                             (=>
                                                (not cmp11$1_0)
                                                (let
                                                   ((s1$2_0 s1$2_0_old)
                                                    (s2$2_0 s2$2_0_old)
                                                    (n$2_0 n$2_0_old))
                                                   (let
                                                      ((HEAP$2 HEAP$2_old)
                                                       (add.ptr$2_0 (+ s1$2_0 n$2_0))
                                                       (a.0$2_0 s1$2_0))
                                                      (let
                                                         ((b.0$2_0 s2$2_0)
                                                          (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                         (=>
                                                            cmp$2_0
                                                            (let
                                                               ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                               (let
                                                                  ((conv$2_0 _$2_0)
                                                                   (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                  (let
                                                                     ((conv1$2_0 _$2_1))
                                                                     (let
                                                                        ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                        (let
                                                                           ((tobool$2_0 (distinct sub$2_0 0)))
                                                                           (=>
                                                                              tobool$2_0
                                                                              (let
                                                                                 ((retval.0$2_0 sub$2_0))
                                                                                 (let
                                                                                    ((result$2 retval.0$2_0)
                                                                                     (HEAP$2_res HEAP$2))
                                                                                    false))))))))))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (s2.addr.0$1_0 s2$1_0)
                      (s1.addr.0$1_0 s1$1_0))
                     (let
                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0)
                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                        (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                       (let
                                          ((conv10$1_0 _$1_4))
                                          (let
                                             ((cmp11$1_0 (= conv10$1_0 0)))
                                             (=>
                                                (not cmp11$1_0)
                                                (let
                                                   ((s1$2_0 s1$2_0_old)
                                                    (s2$2_0 s2$2_0_old)
                                                    (n$2_0 n$2_0_old))
                                                   (let
                                                      ((HEAP$2 HEAP$2_old)
                                                       (add.ptr$2_0 (+ s1$2_0 n$2_0))
                                                       (a.0$2_0 s1$2_0))
                                                      (let
                                                         ((b.0$2_0 s2$2_0)
                                                          (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                         (=>
                                                            cmp$2_0
                                                            (let
                                                               ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                               (let
                                                                  ((conv$2_0 _$2_0)
                                                                   (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                  (let
                                                                     ((conv1$2_0 _$2_1))
                                                                     (let
                                                                        ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                        (let
                                                                           ((tobool$2_0 (distinct sub$2_0 0)))
                                                                           (=>
                                                                              (not tobool$2_0)
                                                                              (let
                                                                                 ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                                 (let
                                                                                    ((tobool2$2_0 (distinct _$2_2 0)))
                                                                                    (=>
                                                                                       (not tobool2$2_0)
                                                                                       (let
                                                                                          ((retval.0$2_0 0))
                                                                                          (let
                                                                                             ((result$2 retval.0$2_0)
                                                                                              (HEAP$2_res HEAP$2))
                                                                                             false)))))))))))))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (s2.addr.0$1_0 s2$1_0)
                      (s1.addr.0$1_0 s1$1_0))
                     (let
                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0)
                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                        (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                       (let
                                          ((conv10$1_0 _$1_4))
                                          (let
                                             ((cmp11$1_0 (= conv10$1_0 0)))
                                             (=>
                                                (not cmp11$1_0)
                                                (let
                                                   ((s1$2_0 s1$2_0_old)
                                                    (s2$2_0 s2$2_0_old)
                                                    (n$2_0 n$2_0_old))
                                                   (let
                                                      ((HEAP$2 HEAP$2_old)
                                                       (add.ptr$2_0 (+ s1$2_0 n$2_0))
                                                       (a.0$2_0 s1$2_0))
                                                      (let
                                                         ((b.0$2_0 s2$2_0)
                                                          (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                         (=>
                                                            (not cmp$2_0)
                                                            (let
                                                               ((retval.0$2_0 0))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  false))))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((retval.0$1_0 0))
                     (let
                        ((result$1 retval.0$1_0)
                         (HEAP$1_res HEAP$1)
                         (s1$2_0 s1$2_0_old)
                         (s2$2_0 s2$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (add.ptr$2_0 (+ s1$2_0 n$2_0))
                            (a.0$2_0 s1$2_0))
                           (let
                              ((b.0$2_0 s2$2_0)
                               (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((_$2_0 (select HEAP$2 a.0$2_0)))
                                    (let
                                       ((conv$2_0 _$2_0)
                                        (_$2_1 (select HEAP$2 b.0$2_0)))
                                       (let
                                          ((conv1$2_0 _$2_1))
                                          (let
                                             ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                             (let
                                                ((tobool$2_0 (distinct sub$2_0 0)))
                                                (=>
                                                   tobool$2_0
                                                   (let
                                                      ((retval.0$2_0 sub$2_0))
                                                      (let
                                                         ((result$2 retval.0$2_0)
                                                          (HEAP$2_res HEAP$2))
                                                         (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((retval.0$1_0 0))
                     (let
                        ((result$1 retval.0$1_0)
                         (HEAP$1_res HEAP$1)
                         (s1$2_0 s1$2_0_old)
                         (s2$2_0 s2$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (add.ptr$2_0 (+ s1$2_0 n$2_0))
                            (a.0$2_0 s1$2_0))
                           (let
                              ((b.0$2_0 s2$2_0)
                               (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((_$2_0 (select HEAP$2 a.0$2_0)))
                                    (let
                                       ((conv$2_0 _$2_0)
                                        (_$2_1 (select HEAP$2 b.0$2_0)))
                                       (let
                                          ((conv1$2_0 _$2_1))
                                          (let
                                             ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                             (let
                                                ((tobool$2_0 (distinct sub$2_0 0)))
                                                (=>
                                                   (not tobool$2_0)
                                                   (let
                                                      ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                      (let
                                                         ((tobool2$2_0 (distinct _$2_2 0)))
                                                         (=>
                                                            (not tobool2$2_0)
                                                            (let
                                                               ((retval.0$2_0 0))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  cmp$1_0
                  (let
                     ((retval.0$1_0 0))
                     (let
                        ((result$1 retval.0$1_0)
                         (HEAP$1_res HEAP$1)
                         (s1$2_0 s1$2_0_old)
                         (s2$2_0 s2$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (add.ptr$2_0 (+ s1$2_0 n$2_0))
                            (a.0$2_0 s1$2_0))
                           (let
                              ((b.0$2_0 s2$2_0)
                               (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (s2.addr.0$1_0 s2$1_0)
                      (s1.addr.0$1_0 s1$1_0))
                     (let
                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0)
                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                 (=>
                                    cmp2$1_0
                                    (let
                                       ((_$1_2 (select HEAP$1 s1.addr.0$1_0)))
                                       (let
                                          ((conv5$1_0 _$1_2)
                                           (incdec.ptr6$1_0 (+ incdec.ptr$1_0 (- 1))))
                                          (let
                                             ((_$1_3 (select HEAP$1 incdec.ptr6$1_0)))
                                             (let
                                                ((conv7$1_0 _$1_3))
                                                (let
                                                   ((sub$1_0 (- conv5$1_0 conv7$1_0)))
                                                   (let
                                                      ((retval.0$1_0 sub$1_0))
                                                      (let
                                                         ((result$1 retval.0$1_0)
                                                          (HEAP$1_res HEAP$1)
                                                          (s1$2_0 s1$2_0_old)
                                                          (s2$2_0 s2$2_0_old)
                                                          (n$2_0 n$2_0_old))
                                                         (let
                                                            ((HEAP$2 HEAP$2_old)
                                                             (add.ptr$2_0 (+ s1$2_0 n$2_0))
                                                             (a.0$2_0 s1$2_0))
                                                            (let
                                                               ((b.0$2_0 s2$2_0)
                                                                (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                               (=>
                                                                  cmp$2_0
                                                                  (let
                                                                     ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                                     (let
                                                                        ((conv$2_0 _$2_0)
                                                                         (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                        (let
                                                                           ((conv1$2_0 _$2_1))
                                                                           (let
                                                                              ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                              (let
                                                                                 ((tobool$2_0 (distinct sub$2_0 0)))
                                                                                 (=>
                                                                                    tobool$2_0
                                                                                    (let
                                                                                       ((retval.0$2_0 sub$2_0))
                                                                                       (let
                                                                                          ((result$2 retval.0$2_0)
                                                                                           (HEAP$2_res HEAP$2))
                                                                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (s2.addr.0$1_0 s2$1_0)
                      (s1.addr.0$1_0 s1$1_0))
                     (let
                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0)
                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                 (=>
                                    cmp2$1_0
                                    (let
                                       ((_$1_2 (select HEAP$1 s1.addr.0$1_0)))
                                       (let
                                          ((conv5$1_0 _$1_2)
                                           (incdec.ptr6$1_0 (+ incdec.ptr$1_0 (- 1))))
                                          (let
                                             ((_$1_3 (select HEAP$1 incdec.ptr6$1_0)))
                                             (let
                                                ((conv7$1_0 _$1_3))
                                                (let
                                                   ((sub$1_0 (- conv5$1_0 conv7$1_0)))
                                                   (let
                                                      ((retval.0$1_0 sub$1_0))
                                                      (let
                                                         ((result$1 retval.0$1_0)
                                                          (HEAP$1_res HEAP$1)
                                                          (s1$2_0 s1$2_0_old)
                                                          (s2$2_0 s2$2_0_old)
                                                          (n$2_0 n$2_0_old))
                                                         (let
                                                            ((HEAP$2 HEAP$2_old)
                                                             (add.ptr$2_0 (+ s1$2_0 n$2_0))
                                                             (a.0$2_0 s1$2_0))
                                                            (let
                                                               ((b.0$2_0 s2$2_0)
                                                                (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                               (=>
                                                                  cmp$2_0
                                                                  (let
                                                                     ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                                     (let
                                                                        ((conv$2_0 _$2_0)
                                                                         (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                        (let
                                                                           ((conv1$2_0 _$2_1))
                                                                           (let
                                                                              ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                              (let
                                                                                 ((tobool$2_0 (distinct sub$2_0 0)))
                                                                                 (=>
                                                                                    (not tobool$2_0)
                                                                                    (let
                                                                                       ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                                       (let
                                                                                          ((tobool2$2_0 (distinct _$2_2 0)))
                                                                                          (=>
                                                                                             (not tobool2$2_0)
                                                                                             (let
                                                                                                ((retval.0$2_0 0))
                                                                                                (let
                                                                                                   ((result$2 retval.0$2_0)
                                                                                                    (HEAP$2_res HEAP$2))
                                                                                                   (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (s2.addr.0$1_0 s2$1_0)
                      (s1.addr.0$1_0 s1$1_0))
                     (let
                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0)
                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                 (=>
                                    cmp2$1_0
                                    (let
                                       ((_$1_2 (select HEAP$1 s1.addr.0$1_0)))
                                       (let
                                          ((conv5$1_0 _$1_2)
                                           (incdec.ptr6$1_0 (+ incdec.ptr$1_0 (- 1))))
                                          (let
                                             ((_$1_3 (select HEAP$1 incdec.ptr6$1_0)))
                                             (let
                                                ((conv7$1_0 _$1_3))
                                                (let
                                                   ((sub$1_0 (- conv5$1_0 conv7$1_0)))
                                                   (let
                                                      ((retval.0$1_0 sub$1_0))
                                                      (let
                                                         ((result$1 retval.0$1_0)
                                                          (HEAP$1_res HEAP$1)
                                                          (s1$2_0 s1$2_0_old)
                                                          (s2$2_0 s2$2_0_old)
                                                          (n$2_0 n$2_0_old))
                                                         (let
                                                            ((HEAP$2 HEAP$2_old)
                                                             (add.ptr$2_0 (+ s1$2_0 n$2_0))
                                                             (a.0$2_0 s1$2_0))
                                                            (let
                                                               ((b.0$2_0 s2$2_0)
                                                                (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                               (=>
                                                                  (not cmp$2_0)
                                                                  (let
                                                                     ((retval.0$2_0 0))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (s2.addr.0$1_0 s2$1_0)
                      (s1.addr.0$1_0 s1$1_0))
                     (let
                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0)
                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                        (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                       (let
                                          ((conv10$1_0 _$1_4))
                                          (let
                                             ((cmp11$1_0 (= conv10$1_0 0)))
                                             (=>
                                                cmp11$1_0
                                                (let
                                                   ((retval.0$1_0 0))
                                                   (let
                                                      ((result$1 retval.0$1_0)
                                                       (HEAP$1_res HEAP$1)
                                                       (s1$2_0 s1$2_0_old)
                                                       (s2$2_0 s2$2_0_old)
                                                       (n$2_0 n$2_0_old))
                                                      (let
                                                         ((HEAP$2 HEAP$2_old)
                                                          (add.ptr$2_0 (+ s1$2_0 n$2_0))
                                                          (a.0$2_0 s1$2_0))
                                                         (let
                                                            ((b.0$2_0 s2$2_0)
                                                             (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                            (=>
                                                               cmp$2_0
                                                               (let
                                                                  ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                                  (let
                                                                     ((conv$2_0 _$2_0)
                                                                      (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                     (let
                                                                        ((conv1$2_0 _$2_1))
                                                                        (let
                                                                           ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                           (let
                                                                              ((tobool$2_0 (distinct sub$2_0 0)))
                                                                              (=>
                                                                                 tobool$2_0
                                                                                 (let
                                                                                    ((retval.0$2_0 sub$2_0))
                                                                                    (let
                                                                                       ((result$2 retval.0$2_0)
                                                                                        (HEAP$2_res HEAP$2))
                                                                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (s2.addr.0$1_0 s2$1_0)
                      (s1.addr.0$1_0 s1$1_0))
                     (let
                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0)
                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                        (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                       (let
                                          ((conv10$1_0 _$1_4))
                                          (let
                                             ((cmp11$1_0 (= conv10$1_0 0)))
                                             (=>
                                                cmp11$1_0
                                                (let
                                                   ((retval.0$1_0 0))
                                                   (let
                                                      ((result$1 retval.0$1_0)
                                                       (HEAP$1_res HEAP$1)
                                                       (s1$2_0 s1$2_0_old)
                                                       (s2$2_0 s2$2_0_old)
                                                       (n$2_0 n$2_0_old))
                                                      (let
                                                         ((HEAP$2 HEAP$2_old)
                                                          (add.ptr$2_0 (+ s1$2_0 n$2_0))
                                                          (a.0$2_0 s1$2_0))
                                                         (let
                                                            ((b.0$2_0 s2$2_0)
                                                             (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                            (=>
                                                               cmp$2_0
                                                               (let
                                                                  ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                                  (let
                                                                     ((conv$2_0 _$2_0)
                                                                      (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                     (let
                                                                        ((conv1$2_0 _$2_1))
                                                                        (let
                                                                           ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                           (let
                                                                              ((tobool$2_0 (distinct sub$2_0 0)))
                                                                              (=>
                                                                                 (not tobool$2_0)
                                                                                 (let
                                                                                    ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                                    (let
                                                                                       ((tobool2$2_0 (distinct _$2_2 0)))
                                                                                       (=>
                                                                                          (not tobool2$2_0)
                                                                                          (let
                                                                                             ((retval.0$2_0 0))
                                                                                             (let
                                                                                                ((result$2 retval.0$2_0)
                                                                                                 (HEAP$2_res HEAP$2))
                                                                                                (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (s2.addr.0$1_0 s2$1_0)
                      (s1.addr.0$1_0 s1$1_0))
                     (let
                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0)
                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                        (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                       (let
                                          ((conv10$1_0 _$1_4))
                                          (let
                                             ((cmp11$1_0 (= conv10$1_0 0)))
                                             (=>
                                                cmp11$1_0
                                                (let
                                                   ((retval.0$1_0 0))
                                                   (let
                                                      ((result$1 retval.0$1_0)
                                                       (HEAP$1_res HEAP$1)
                                                       (s1$2_0 s1$2_0_old)
                                                       (s2$2_0 s2$2_0_old)
                                                       (n$2_0 n$2_0_old))
                                                      (let
                                                         ((HEAP$2 HEAP$2_old)
                                                          (add.ptr$2_0 (+ s1$2_0 n$2_0))
                                                          (a.0$2_0 s1$2_0))
                                                         (let
                                                            ((b.0$2_0 s2$2_0)
                                                             (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                            (=>
                                                               (not cmp$2_0)
                                                               (let
                                                                  ((retval.0$2_0 0))
                                                                  (let
                                                                     ((result$2 retval.0$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))
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
                (cmp$1_0 (= n$1_0 0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((n.addr.0$1_0 n$1_0)
                      (s2.addr.0$1_0 s2$1_0)
                      (s1.addr.0$1_0 s1$1_0))
                     (let
                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                        (let
                           ((conv$1_0 _$1_0)
                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                           (let
                              ((conv1$1_0 _$1_1))
                              (let
                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                        (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                       (let
                                          ((conv10$1_0 _$1_4))
                                          (let
                                             ((cmp11$1_0 (= conv10$1_0 0)))
                                             (=>
                                                (not cmp11$1_0)
                                                (let
                                                   ((s1$2_0 s1$2_0_old)
                                                    (s2$2_0 s2$2_0_old)
                                                    (n$2_0 n$2_0_old))
                                                   (let
                                                      ((HEAP$2 HEAP$2_old)
                                                       (add.ptr$2_0 (+ s1$2_0 n$2_0))
                                                       (a.0$2_0 s1$2_0))
                                                      (let
                                                         ((b.0$2_0 s2$2_0)
                                                          (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                         (=>
                                                            cmp$2_0
                                                            (let
                                                               ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                               (let
                                                                  ((conv$2_0 _$2_0)
                                                                   (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                  (let
                                                                     ((conv1$2_0 _$2_1))
                                                                     (let
                                                                        ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                        (let
                                                                           ((tobool$2_0 (distinct sub$2_0 0)))
                                                                           (=>
                                                                              (not tobool$2_0)
                                                                              (let
                                                                                 ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                                 (let
                                                                                    ((tobool2$2_0 (distinct _$2_2 0)))
                                                                                    (=>
                                                                                       tobool2$2_0
                                                                                       (forall
                                                                                          ((i1 Int)
                                                                                           (i2 Int))
                                                                                          (INV_MAIN_42 incdec.ptr$1_0 incdec.ptr9$1_0 n.addr.0$1_0 i1 (select HEAP$1 i1) a.0$2_0 add.ptr$2_0 b.0$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))
(assert
   (forall
      ((incdec.ptr$1_0_old Int)
       (incdec.ptr9$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr9$1_0 incdec.ptr9$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (dec$1_0 (+ n.addr.0$1_0 (- 1))))
               (let
                  ((cmp15$1_0 (distinct dec$1_0 0)))
                  (=>
                     cmp15$1_0
                     (let
                        ((n.addr.0$1_0 dec$1_0)
                         (s2.addr.0$1_0 incdec.ptr$1_0)
                         (s1.addr.0$1_0 incdec.ptr9$1_0))
                        (let
                           ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                           (let
                              ((conv$1_0 _$1_0)
                               (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                               (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                              (let
                                 ((conv1$1_0 _$1_1))
                                 (let
                                    ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                    (=>
                                       cmp2$1_0
                                       (let
                                          ((_$1_2 (select HEAP$1 s1.addr.0$1_0)))
                                          (let
                                             ((conv5$1_0 _$1_2)
                                              (incdec.ptr6$1_0 (+ incdec.ptr$1_0 (- 1))))
                                             (let
                                                ((_$1_3 (select HEAP$1 incdec.ptr6$1_0)))
                                                (let
                                                   ((conv7$1_0 _$1_3))
                                                   (let
                                                      ((sub$1_0 (- conv5$1_0 conv7$1_0)))
                                                      (let
                                                         ((retval.0$1_0 sub$1_0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (a.0$2_0 a.0$2_0_old))
                                                            (let
                                                               ((add.ptr$2_0 add.ptr$2_0_old)
                                                                (b.0$2_0 b.0$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (incdec.ptr$2_0 (+ a.0$2_0 1)))
                                                               (let
                                                                  ((incdec.ptr5$2_0 (+ b.0$2_0 1))
                                                                   (a.0$2_0 incdec.ptr$2_0))
                                                                  (let
                                                                     ((b.0$2_0 incdec.ptr5$2_0)
                                                                      (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                                     (=>
                                                                        cmp$2_0
                                                                        (let
                                                                           ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                                           (let
                                                                              ((conv$2_0 _$2_0)
                                                                               (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                              (let
                                                                                 ((conv1$2_0 _$2_1))
                                                                                 (let
                                                                                    ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                                    (let
                                                                                       ((tobool$2_0 (distinct sub$2_0 0)))
                                                                                       (=>
                                                                                          tobool$2_0
                                                                                          (let
                                                                                             ((retval.0$2_0 sub$2_0))
                                                                                             (let
                                                                                                ((result$2 retval.0$2_0)
                                                                                                 (HEAP$2_res HEAP$2))
                                                                                                (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((incdec.ptr$1_0_old Int)
       (incdec.ptr9$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr9$1_0 incdec.ptr9$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (dec$1_0 (+ n.addr.0$1_0 (- 1))))
               (let
                  ((cmp15$1_0 (distinct dec$1_0 0)))
                  (=>
                     cmp15$1_0
                     (let
                        ((n.addr.0$1_0 dec$1_0)
                         (s2.addr.0$1_0 incdec.ptr$1_0)
                         (s1.addr.0$1_0 incdec.ptr9$1_0))
                        (let
                           ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                           (let
                              ((conv$1_0 _$1_0)
                               (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                               (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                              (let
                                 ((conv1$1_0 _$1_1))
                                 (let
                                    ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                    (=>
                                       cmp2$1_0
                                       (let
                                          ((_$1_2 (select HEAP$1 s1.addr.0$1_0)))
                                          (let
                                             ((conv5$1_0 _$1_2)
                                              (incdec.ptr6$1_0 (+ incdec.ptr$1_0 (- 1))))
                                             (let
                                                ((_$1_3 (select HEAP$1 incdec.ptr6$1_0)))
                                                (let
                                                   ((conv7$1_0 _$1_3))
                                                   (let
                                                      ((sub$1_0 (- conv5$1_0 conv7$1_0)))
                                                      (let
                                                         ((retval.0$1_0 sub$1_0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (a.0$2_0 a.0$2_0_old))
                                                            (let
                                                               ((add.ptr$2_0 add.ptr$2_0_old)
                                                                (b.0$2_0 b.0$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (incdec.ptr$2_0 (+ a.0$2_0 1)))
                                                               (let
                                                                  ((incdec.ptr5$2_0 (+ b.0$2_0 1))
                                                                   (a.0$2_0 incdec.ptr$2_0))
                                                                  (let
                                                                     ((b.0$2_0 incdec.ptr5$2_0)
                                                                      (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                                     (=>
                                                                        cmp$2_0
                                                                        (let
                                                                           ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                                           (let
                                                                              ((conv$2_0 _$2_0)
                                                                               (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                              (let
                                                                                 ((conv1$2_0 _$2_1))
                                                                                 (let
                                                                                    ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                                    (let
                                                                                       ((tobool$2_0 (distinct sub$2_0 0)))
                                                                                       (=>
                                                                                          (not tobool$2_0)
                                                                                          (let
                                                                                             ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                                             (let
                                                                                                ((tobool2$2_0 (distinct _$2_2 0)))
                                                                                                (=>
                                                                                                   (not tobool2$2_0)
                                                                                                   (let
                                                                                                      ((retval.0$2_0 0))
                                                                                                      (let
                                                                                                         ((result$2 retval.0$2_0)
                                                                                                          (HEAP$2_res HEAP$2))
                                                                                                         (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((incdec.ptr$1_0_old Int)
       (incdec.ptr9$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr9$1_0 incdec.ptr9$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (dec$1_0 (+ n.addr.0$1_0 (- 1))))
               (let
                  ((cmp15$1_0 (distinct dec$1_0 0)))
                  (=>
                     cmp15$1_0
                     (let
                        ((n.addr.0$1_0 dec$1_0)
                         (s2.addr.0$1_0 incdec.ptr$1_0)
                         (s1.addr.0$1_0 incdec.ptr9$1_0))
                        (let
                           ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                           (let
                              ((conv$1_0 _$1_0)
                               (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                               (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                              (let
                                 ((conv1$1_0 _$1_1))
                                 (let
                                    ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                    (=>
                                       cmp2$1_0
                                       (let
                                          ((_$1_2 (select HEAP$1 s1.addr.0$1_0)))
                                          (let
                                             ((conv5$1_0 _$1_2)
                                              (incdec.ptr6$1_0 (+ incdec.ptr$1_0 (- 1))))
                                             (let
                                                ((_$1_3 (select HEAP$1 incdec.ptr6$1_0)))
                                                (let
                                                   ((conv7$1_0 _$1_3))
                                                   (let
                                                      ((sub$1_0 (- conv5$1_0 conv7$1_0)))
                                                      (let
                                                         ((retval.0$1_0 sub$1_0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (a.0$2_0 a.0$2_0_old))
                                                            (let
                                                               ((add.ptr$2_0 add.ptr$2_0_old)
                                                                (b.0$2_0 b.0$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (incdec.ptr$2_0 (+ a.0$2_0 1)))
                                                               (let
                                                                  ((incdec.ptr5$2_0 (+ b.0$2_0 1))
                                                                   (a.0$2_0 incdec.ptr$2_0))
                                                                  (let
                                                                     ((b.0$2_0 incdec.ptr5$2_0)
                                                                      (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                                     (=>
                                                                        (not cmp$2_0)
                                                                        (let
                                                                           ((retval.0$2_0 0))
                                                                           (let
                                                                              ((result$2 retval.0$2_0)
                                                                               (HEAP$2_res HEAP$2))
                                                                              (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))
(assert
   (forall
      ((incdec.ptr$1_0_old Int)
       (incdec.ptr9$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr9$1_0 incdec.ptr9$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (dec$1_0 (+ n.addr.0$1_0 (- 1))))
               (let
                  ((cmp15$1_0 (distinct dec$1_0 0)))
                  (=>
                     cmp15$1_0
                     (let
                        ((n.addr.0$1_0 dec$1_0)
                         (s2.addr.0$1_0 incdec.ptr$1_0)
                         (s1.addr.0$1_0 incdec.ptr9$1_0))
                        (let
                           ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                           (let
                              ((conv$1_0 _$1_0)
                               (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                               (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                              (let
                                 ((conv1$1_0 _$1_1))
                                 (let
                                    ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                    (=>
                                       (not cmp2$1_0)
                                       (let
                                          ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                           (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                          (let
                                             ((conv10$1_0 _$1_4))
                                             (let
                                                ((cmp11$1_0 (= conv10$1_0 0)))
                                                (=>
                                                   cmp11$1_0
                                                   (let
                                                      ((retval.0$1_0 0))
                                                      (let
                                                         ((result$1 retval.0$1_0)
                                                          (HEAP$1_res HEAP$1)
                                                          (a.0$2_0 a.0$2_0_old))
                                                         (let
                                                            ((add.ptr$2_0 add.ptr$2_0_old)
                                                             (b.0$2_0 b.0$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (incdec.ptr$2_0 (+ a.0$2_0 1)))
                                                            (let
                                                               ((incdec.ptr5$2_0 (+ b.0$2_0 1))
                                                                (a.0$2_0 incdec.ptr$2_0))
                                                               (let
                                                                  ((b.0$2_0 incdec.ptr5$2_0)
                                                                   (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                                  (=>
                                                                     cmp$2_0
                                                                     (let
                                                                        ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                                        (let
                                                                           ((conv$2_0 _$2_0)
                                                                            (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                           (let
                                                                              ((conv1$2_0 _$2_1))
                                                                              (let
                                                                                 ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                                 (let
                                                                                    ((tobool$2_0 (distinct sub$2_0 0)))
                                                                                    (=>
                                                                                       tobool$2_0
                                                                                       (let
                                                                                          ((retval.0$2_0 sub$2_0))
                                                                                          (let
                                                                                             ((result$2 retval.0$2_0)
                                                                                              (HEAP$2_res HEAP$2))
                                                                                             (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))
(assert
   (forall
      ((incdec.ptr$1_0_old Int)
       (incdec.ptr9$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr9$1_0 incdec.ptr9$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (dec$1_0 (+ n.addr.0$1_0 (- 1))))
               (let
                  ((cmp15$1_0 (distinct dec$1_0 0)))
                  (=>
                     cmp15$1_0
                     (let
                        ((n.addr.0$1_0 dec$1_0)
                         (s2.addr.0$1_0 incdec.ptr$1_0)
                         (s1.addr.0$1_0 incdec.ptr9$1_0))
                        (let
                           ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                           (let
                              ((conv$1_0 _$1_0)
                               (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                               (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                              (let
                                 ((conv1$1_0 _$1_1))
                                 (let
                                    ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                    (=>
                                       (not cmp2$1_0)
                                       (let
                                          ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                           (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                          (let
                                             ((conv10$1_0 _$1_4))
                                             (let
                                                ((cmp11$1_0 (= conv10$1_0 0)))
                                                (=>
                                                   cmp11$1_0
                                                   (let
                                                      ((retval.0$1_0 0))
                                                      (let
                                                         ((result$1 retval.0$1_0)
                                                          (HEAP$1_res HEAP$1)
                                                          (a.0$2_0 a.0$2_0_old))
                                                         (let
                                                            ((add.ptr$2_0 add.ptr$2_0_old)
                                                             (b.0$2_0 b.0$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (incdec.ptr$2_0 (+ a.0$2_0 1)))
                                                            (let
                                                               ((incdec.ptr5$2_0 (+ b.0$2_0 1))
                                                                (a.0$2_0 incdec.ptr$2_0))
                                                               (let
                                                                  ((b.0$2_0 incdec.ptr5$2_0)
                                                                   (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                                  (=>
                                                                     cmp$2_0
                                                                     (let
                                                                        ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                                        (let
                                                                           ((conv$2_0 _$2_0)
                                                                            (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                           (let
                                                                              ((conv1$2_0 _$2_1))
                                                                              (let
                                                                                 ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                                 (let
                                                                                    ((tobool$2_0 (distinct sub$2_0 0)))
                                                                                    (=>
                                                                                       (not tobool$2_0)
                                                                                       (let
                                                                                          ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                                          (let
                                                                                             ((tobool2$2_0 (distinct _$2_2 0)))
                                                                                             (=>
                                                                                                (not tobool2$2_0)
                                                                                                (let
                                                                                                   ((retval.0$2_0 0))
                                                                                                   (let
                                                                                                      ((result$2 retval.0$2_0)
                                                                                                       (HEAP$2_res HEAP$2))
                                                                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((incdec.ptr$1_0_old Int)
       (incdec.ptr9$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr9$1_0 incdec.ptr9$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (dec$1_0 (+ n.addr.0$1_0 (- 1))))
               (let
                  ((cmp15$1_0 (distinct dec$1_0 0)))
                  (=>
                     cmp15$1_0
                     (let
                        ((n.addr.0$1_0 dec$1_0)
                         (s2.addr.0$1_0 incdec.ptr$1_0)
                         (s1.addr.0$1_0 incdec.ptr9$1_0))
                        (let
                           ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                           (let
                              ((conv$1_0 _$1_0)
                               (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                               (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                              (let
                                 ((conv1$1_0 _$1_1))
                                 (let
                                    ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                    (=>
                                       (not cmp2$1_0)
                                       (let
                                          ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                           (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                          (let
                                             ((conv10$1_0 _$1_4))
                                             (let
                                                ((cmp11$1_0 (= conv10$1_0 0)))
                                                (=>
                                                   cmp11$1_0
                                                   (let
                                                      ((retval.0$1_0 0))
                                                      (let
                                                         ((result$1 retval.0$1_0)
                                                          (HEAP$1_res HEAP$1)
                                                          (a.0$2_0 a.0$2_0_old))
                                                         (let
                                                            ((add.ptr$2_0 add.ptr$2_0_old)
                                                             (b.0$2_0 b.0$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (incdec.ptr$2_0 (+ a.0$2_0 1)))
                                                            (let
                                                               ((incdec.ptr5$2_0 (+ b.0$2_0 1))
                                                                (a.0$2_0 incdec.ptr$2_0))
                                                               (let
                                                                  ((b.0$2_0 incdec.ptr5$2_0)
                                                                   (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                                  (=>
                                                                     (not cmp$2_0)
                                                                     (let
                                                                        ((retval.0$2_0 0))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((incdec.ptr$1_0_old Int)
       (incdec.ptr9$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr9$1_0 incdec.ptr9$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (dec$1_0 (+ n.addr.0$1_0 (- 1))))
               (let
                  ((cmp15$1_0 (distinct dec$1_0 0)))
                  (=>
                     (not cmp15$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (a.0$2_0 a.0$2_0_old))
                           (let
                              ((add.ptr$2_0 add.ptr$2_0_old)
                               (b.0$2_0 b.0$2_0_old)
                               (HEAP$2 HEAP$2_old)
                               (incdec.ptr$2_0 (+ a.0$2_0 1)))
                              (let
                                 ((incdec.ptr5$2_0 (+ b.0$2_0 1))
                                  (a.0$2_0 incdec.ptr$2_0))
                                 (let
                                    ((b.0$2_0 incdec.ptr5$2_0)
                                     (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                    (=>
                                       cmp$2_0
                                       (let
                                          ((_$2_0 (select HEAP$2 a.0$2_0)))
                                          (let
                                             ((conv$2_0 _$2_0)
                                              (_$2_1 (select HEAP$2 b.0$2_0)))
                                             (let
                                                ((conv1$2_0 _$2_1))
                                                (let
                                                   ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                   (let
                                                      ((tobool$2_0 (distinct sub$2_0 0)))
                                                      (=>
                                                         tobool$2_0
                                                         (let
                                                            ((retval.0$2_0 sub$2_0))
                                                            (let
                                                               ((result$2 retval.0$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((incdec.ptr$1_0_old Int)
       (incdec.ptr9$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr9$1_0 incdec.ptr9$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (dec$1_0 (+ n.addr.0$1_0 (- 1))))
               (let
                  ((cmp15$1_0 (distinct dec$1_0 0)))
                  (=>
                     (not cmp15$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (a.0$2_0 a.0$2_0_old))
                           (let
                              ((add.ptr$2_0 add.ptr$2_0_old)
                               (b.0$2_0 b.0$2_0_old)
                               (HEAP$2 HEAP$2_old)
                               (incdec.ptr$2_0 (+ a.0$2_0 1)))
                              (let
                                 ((incdec.ptr5$2_0 (+ b.0$2_0 1))
                                  (a.0$2_0 incdec.ptr$2_0))
                                 (let
                                    ((b.0$2_0 incdec.ptr5$2_0)
                                     (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                    (=>
                                       cmp$2_0
                                       (let
                                          ((_$2_0 (select HEAP$2 a.0$2_0)))
                                          (let
                                             ((conv$2_0 _$2_0)
                                              (_$2_1 (select HEAP$2 b.0$2_0)))
                                             (let
                                                ((conv1$2_0 _$2_1))
                                                (let
                                                   ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                   (let
                                                      ((tobool$2_0 (distinct sub$2_0 0)))
                                                      (=>
                                                         (not tobool$2_0)
                                                         (let
                                                            ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                            (let
                                                               ((tobool2$2_0 (distinct _$2_2 0)))
                                                               (=>
                                                                  (not tobool2$2_0)
                                                                  (let
                                                                     ((retval.0$2_0 0))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((incdec.ptr$1_0_old Int)
       (incdec.ptr9$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr9$1_0 incdec.ptr9$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (dec$1_0 (+ n.addr.0$1_0 (- 1))))
               (let
                  ((cmp15$1_0 (distinct dec$1_0 0)))
                  (=>
                     (not cmp15$1_0)
                     (let
                        ((retval.0$1_0 0))
                        (let
                           ((result$1 retval.0$1_0)
                            (HEAP$1_res HEAP$1)
                            (a.0$2_0 a.0$2_0_old))
                           (let
                              ((add.ptr$2_0 add.ptr$2_0_old)
                               (b.0$2_0 b.0$2_0_old)
                               (HEAP$2 HEAP$2_old)
                               (incdec.ptr$2_0 (+ a.0$2_0 1)))
                              (let
                                 ((incdec.ptr5$2_0 (+ b.0$2_0 1))
                                  (a.0$2_0 incdec.ptr$2_0))
                                 (let
                                    ((b.0$2_0 incdec.ptr5$2_0)
                                     (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                    (=>
                                       (not cmp$2_0)
                                       (let
                                          ((retval.0$2_0 0))
                                          (let
                                             ((result$2 retval.0$2_0)
                                              (HEAP$2_res HEAP$2))
                                             (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))
(assert
   (forall
      ((incdec.ptr$1_0_old Int)
       (incdec.ptr9$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr9$1_0 incdec.ptr9$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (dec$1_0 (+ n.addr.0$1_0 (- 1))))
               (let
                  ((cmp15$1_0 (distinct dec$1_0 0)))
                  (=>
                     cmp15$1_0
                     (let
                        ((n.addr.0$1_0 dec$1_0)
                         (s2.addr.0$1_0 incdec.ptr$1_0)
                         (s1.addr.0$1_0 incdec.ptr9$1_0))
                        (let
                           ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                           (let
                              ((conv$1_0 _$1_0)
                               (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                               (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                              (let
                                 ((conv1$1_0 _$1_1))
                                 (let
                                    ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                    (=>
                                       (not cmp2$1_0)
                                       (let
                                          ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                           (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                          (let
                                             ((conv10$1_0 _$1_4))
                                             (let
                                                ((cmp11$1_0 (= conv10$1_0 0)))
                                                (=>
                                                   (not cmp11$1_0)
                                                   (let
                                                      ((a.0$2_0 a.0$2_0_old))
                                                      (let
                                                         ((add.ptr$2_0 add.ptr$2_0_old)
                                                          (b.0$2_0 b.0$2_0_old)
                                                          (HEAP$2 HEAP$2_old)
                                                          (incdec.ptr$2_0 (+ a.0$2_0 1)))
                                                         (let
                                                            ((incdec.ptr5$2_0 (+ b.0$2_0 1))
                                                             (a.0$2_0 incdec.ptr$2_0))
                                                            (let
                                                               ((b.0$2_0 incdec.ptr5$2_0)
                                                                (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                               (=>
                                                                  cmp$2_0
                                                                  (let
                                                                     ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                                     (let
                                                                        ((conv$2_0 _$2_0)
                                                                         (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                        (let
                                                                           ((conv1$2_0 _$2_1))
                                                                           (let
                                                                              ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                              (let
                                                                                 ((tobool$2_0 (distinct sub$2_0 0)))
                                                                                 (=>
                                                                                    (not tobool$2_0)
                                                                                    (let
                                                                                       ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                                       (let
                                                                                          ((tobool2$2_0 (distinct _$2_2 0)))
                                                                                          (=>
                                                                                             tobool2$2_0
                                                                                             (forall
                                                                                                ((i1 Int)
                                                                                                 (i2 Int))
                                                                                                (INV_MAIN_42 incdec.ptr$1_0 incdec.ptr9$1_0 n.addr.0$1_0 i1 (select HEAP$1 i1) a.0$2_0 add.ptr$2_0 b.0$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((incdec.ptr$1_0_old Int)
       (incdec.ptr9$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr9$1_0 incdec.ptr9$1_0_old)
             (n.addr.0$1_0 n.addr.0$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (dec$1_0 (+ n.addr.0$1_0 (- 1))))
               (let
                  ((cmp15$1_0 (distinct dec$1_0 0)))
                  (=>
                     cmp15$1_0
                     (let
                        ((n.addr.0$1_0 dec$1_0)
                         (s2.addr.0$1_0 incdec.ptr$1_0)
                         (s1.addr.0$1_0 incdec.ptr9$1_0))
                        (let
                           ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                           (let
                              ((conv$1_0 _$1_0)
                               (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                               (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                              (let
                                 ((conv1$1_0 _$1_1))
                                 (let
                                    ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                    (=>
                                       (not cmp2$1_0)
                                       (let
                                          ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                           (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                          (let
                                             ((conv10$1_0 _$1_4))
                                             (let
                                                ((cmp11$1_0 (= conv10$1_0 0)))
                                                (=>
                                                   (not cmp11$1_0)
                                                   (=>
                                                      (let
                                                         ((a.0$2_0 a.0$2_0_old))
                                                         (let
                                                            ((add.ptr$2_0 add.ptr$2_0_old)
                                                             (b.0$2_0 b.0$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (incdec.ptr$2_0 (+ a.0$2_0 1)))
                                                            (let
                                                               ((incdec.ptr5$2_0 (+ b.0$2_0 1))
                                                                (a.0$2_0 incdec.ptr$2_0))
                                                               (let
                                                                  ((b.0$2_0 incdec.ptr5$2_0)
                                                                   (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                                                                  (=>
                                                                     cmp$2_0
                                                                     (let
                                                                        ((_$2_0 (select HEAP$2 a.0$2_0)))
                                                                        (let
                                                                           ((conv$2_0 _$2_0)
                                                                            (_$2_1 (select HEAP$2 b.0$2_0)))
                                                                           (let
                                                                              ((conv1$2_0 _$2_1))
                                                                              (let
                                                                                 ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                                                                 (let
                                                                                    ((tobool$2_0 (distinct sub$2_0 0)))
                                                                                    (=>
                                                                                       (not tobool$2_0)
                                                                                       (let
                                                                                          ((_$2_2 (select HEAP$2 a.0$2_0)))
                                                                                          (let
                                                                                             ((tobool2$2_0 (distinct _$2_2 0)))
                                                                                             (not tobool2$2_0))))))))))))))
                                                      (forall
                                                         ((i1 Int)
                                                          (i2_old Int))
                                                         (INV_MAIN_42 incdec.ptr$1_0 incdec.ptr9$1_0 n.addr.0$1_0 i1 (select HEAP$1 i1) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))))))))))
(assert
   (forall
      ((incdec.ptr$1_0_old Int)
       (incdec.ptr9$1_0_old Int)
       (n.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (add.ptr$2_0_old Int)
       (b.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0_old add.ptr$2_0_old b.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((a.0$2_0 a.0$2_0_old))
            (let
               ((add.ptr$2_0 add.ptr$2_0_old)
                (b.0$2_0 b.0$2_0_old)
                (HEAP$2 HEAP$2_old)
                (incdec.ptr$2_0 (+ a.0$2_0 1)))
               (let
                  ((incdec.ptr5$2_0 (+ b.0$2_0 1))
                   (a.0$2_0 incdec.ptr$2_0))
                  (let
                     ((b.0$2_0 incdec.ptr5$2_0)
                      (cmp$2_0 (distinct a.0$2_0 add.ptr$2_0)))
                     (=>
                        cmp$2_0
                        (let
                           ((_$2_0 (select HEAP$2 a.0$2_0)))
                           (let
                              ((conv$2_0 _$2_0)
                               (_$2_1 (select HEAP$2 b.0$2_0)))
                              (let
                                 ((conv1$2_0 _$2_1))
                                 (let
                                    ((sub$2_0 (- conv$2_0 conv1$2_0)))
                                    (let
                                       ((tobool$2_0 (distinct sub$2_0 0)))
                                       (=>
                                          (not tobool$2_0)
                                          (let
                                             ((_$2_2 (select HEAP$2 a.0$2_0)))
                                             (let
                                                ((tobool2$2_0 (distinct _$2_2 0)))
                                                (=>
                                                   tobool2$2_0
                                                   (=>
                                                      (let
                                                         ((incdec.ptr$1_0 incdec.ptr$1_0_old)
                                                          (incdec.ptr9$1_0 incdec.ptr9$1_0_old)
                                                          (n.addr.0$1_0 n.addr.0$1_0_old))
                                                         (let
                                                            ((HEAP$1 HEAP$1_old)
                                                             (dec$1_0 (+ n.addr.0$1_0 (- 1))))
                                                            (let
                                                               ((cmp15$1_0 (distinct dec$1_0 0)))
                                                               (=>
                                                                  cmp15$1_0
                                                                  (let
                                                                     ((n.addr.0$1_0 dec$1_0)
                                                                      (s2.addr.0$1_0 incdec.ptr$1_0)
                                                                      (s1.addr.0$1_0 incdec.ptr9$1_0))
                                                                     (let
                                                                        ((_$1_0 (select HEAP$1 s1.addr.0$1_0)))
                                                                        (let
                                                                           ((conv$1_0 _$1_0)
                                                                            (incdec.ptr$1_0 (+ s2.addr.0$1_0 1))
                                                                            (_$1_1 (select HEAP$1 s2.addr.0$1_0)))
                                                                           (let
                                                                              ((conv1$1_0 _$1_1))
                                                                              (let
                                                                                 ((cmp2$1_0 (distinct conv$1_0 conv1$1_0)))
                                                                                 (=>
                                                                                    (not cmp2$1_0)
                                                                                    (let
                                                                                       ((incdec.ptr9$1_0 (+ s1.addr.0$1_0 1))
                                                                                        (_$1_4 (select HEAP$1 s1.addr.0$1_0)))
                                                                                       (let
                                                                                          ((conv10$1_0 _$1_4))
                                                                                          (let
                                                                                             ((cmp11$1_0 (= conv10$1_0 0)))
                                                                                             (not (not cmp11$1_0)))))))))))))))
                                                      (forall
                                                         ((i1_old Int)
                                                          (i2 Int))
                                                         (INV_MAIN_42 incdec.ptr$1_0_old incdec.ptr9$1_0_old n.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) a.0$2_0 add.ptr$2_0 b.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))
(check-sat)
(get-model)
