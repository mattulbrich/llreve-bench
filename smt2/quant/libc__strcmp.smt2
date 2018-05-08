;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((p1$1_0 Int)
    (p2$1_0 Int)
    (HEAP$1 (Array Int Int))
    (s1$2_0 Int)
    (s2$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= p1$1_0 s1$2_0)
      (= p2$1_0 s2$2_0)
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
; :annot (INV_MAIN_42 _$1_0 _$1_1 incdec.ptr$1_0 incdec.ptr1$1_0 HEAP$1 incdec.ptr$2_0 incdec.ptr3$2_0 HEAP$2)
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
      ((p1$1_0_old Int)
       (p2$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s1$2_0_old Int)
       (s2$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV p1$1_0_old p2$1_0_old HEAP$1_old s1$2_0_old s2$2_0_old HEAP$2_old)
         (let
            ((p1$1_0 p1$1_0_old))
            (let
               ((p2$1_0 p2$1_0_old)
                (HEAP$1 HEAP$1_old)
                (s1.0$1_0 p1$1_0))
               (let
                  ((s2.0$1_0 p2$1_0)
                   (incdec.ptr$1_0 (+ s1.0$1_0 1))
                   (_$1_0 (select HEAP$1 s1.0$1_0)))
                  (let
                     ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                      (_$1_1 (select HEAP$1 s2.0$1_0))
                      (conv$1_0 _$1_0))
                     (let
                        ((cmp$1_0 (= conv$1_0 0)))
                        (=>
                           cmp$1_0
                           (let
                              ((conv9$1_0 _$1_0)
                               (conv10$1_0 _$1_1))
                              (let
                                 ((sub11$1_0 (- conv9$1_0 conv10$1_0)))
                                 (let
                                    ((result$1 sub11$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (s1$2_0 s1$2_0_old)
                                     (s2$2_0 s2$2_0_old))
                                    (let
                                       ((HEAP$2 HEAP$2_old)
                                        (s2.addr.0$2_0 s2$2_0)
                                        (s1.addr.0$2_0 s1$2_0))
                                       (let
                                          ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                          (let
                                             ((conv$2_0 _$2_0)
                                              (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                              (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                             (let
                                                ((conv1$2_0 _$2_1))
                                                (let
                                                   ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                   (=>
                                                      cmp$2_0
                                                      (let
                                                         ((incdec.ptr3$2_0 (+ s1.addr.0$2_0 1))
                                                          (_$2_2 (select HEAP$2 s1.addr.0$2_0)))
                                                         (let
                                                            ((conv4$2_0 _$2_2))
                                                            (let
                                                               ((cmp5$2_0 (= conv4$2_0 0)))
                                                               (not (not cmp5$2_0)))))))))))))))))))))))
(assert
   (forall
      ((p1$1_0_old Int)
       (p2$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s1$2_0_old Int)
       (s2$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV p1$1_0_old p2$1_0_old HEAP$1_old s1$2_0_old s2$2_0_old HEAP$2_old)
         (let
            ((p1$1_0 p1$1_0_old))
            (let
               ((p2$1_0 p2$1_0_old)
                (HEAP$1 HEAP$1_old)
                (s1.0$1_0 p1$1_0))
               (let
                  ((s2.0$1_0 p2$1_0)
                   (incdec.ptr$1_0 (+ s1.0$1_0 1))
                   (_$1_0 (select HEAP$1 s1.0$1_0)))
                  (let
                     ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                      (_$1_1 (select HEAP$1 s2.0$1_0))
                      (conv$1_0 _$1_0))
                     (let
                        ((cmp$1_0 (= conv$1_0 0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((conv5$1_0 _$1_0)
                               (conv6$1_0 _$1_1))
                              (let
                                 ((cmp7$1_0 (= conv5$1_0 conv6$1_0)))
                                 (=>
                                    (not cmp7$1_0)
                                    (let
                                       ((conv9$1_0 _$1_0)
                                        (conv10$1_0 _$1_1))
                                       (let
                                          ((sub11$1_0 (- conv9$1_0 conv10$1_0)))
                                          (let
                                             ((result$1 sub11$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (s1$2_0 s1$2_0_old)
                                              (s2$2_0 s2$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (s2.addr.0$2_0 s2$2_0)
                                                 (s1.addr.0$2_0 s1$2_0))
                                                (let
                                                   ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                                   (let
                                                      ((conv$2_0 _$2_0)
                                                       (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                                       (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                                      (let
                                                         ((conv1$2_0 _$2_1))
                                                         (let
                                                            ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                            (=>
                                                               cmp$2_0
                                                               (let
                                                                  ((incdec.ptr3$2_0 (+ s1.addr.0$2_0 1))
                                                                   (_$2_2 (select HEAP$2 s1.addr.0$2_0)))
                                                                  (let
                                                                     ((conv4$2_0 _$2_2))
                                                                     (let
                                                                        ((cmp5$2_0 (= conv4$2_0 0)))
                                                                        (not (not cmp5$2_0))))))))))))))))))))))))))
(assert
   (forall
      ((p1$1_0_old Int)
       (p2$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s1$2_0_old Int)
       (s2$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV p1$1_0_old p2$1_0_old HEAP$1_old s1$2_0_old s2$2_0_old HEAP$2_old)
         (let
            ((p1$1_0 p1$1_0_old))
            (let
               ((p2$1_0 p2$1_0_old)
                (HEAP$1 HEAP$1_old)
                (s1.0$1_0 p1$1_0))
               (let
                  ((s2.0$1_0 p2$1_0)
                   (incdec.ptr$1_0 (+ s1.0$1_0 1))
                   (_$1_0 (select HEAP$1 s1.0$1_0)))
                  (let
                     ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                      (_$1_1 (select HEAP$1 s2.0$1_0))
                      (conv$1_0 _$1_0))
                     (let
                        ((cmp$1_0 (= conv$1_0 0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((conv5$1_0 _$1_0)
                               (conv6$1_0 _$1_1))
                              (let
                                 ((cmp7$1_0 (= conv5$1_0 conv6$1_0)))
                                 (=>
                                    cmp7$1_0
                                    (let
                                       ((s1$2_0 s1$2_0_old)
                                        (s2$2_0 s2$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (s2.addr.0$2_0 s2$2_0)
                                           (s1.addr.0$2_0 s1$2_0))
                                          (let
                                             ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                             (let
                                                ((conv$2_0 _$2_0)
                                                 (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                                 (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                                (let
                                                   ((conv1$2_0 _$2_1))
                                                   (let
                                                      ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((incdec.ptr3$2_0 (+ s1.addr.0$2_0 1))
                                                             (_$2_2 (select HEAP$2 s1.addr.0$2_0)))
                                                            (let
                                                               ((conv4$2_0 _$2_2))
                                                               (let
                                                                  ((cmp5$2_0 (= conv4$2_0 0)))
                                                                  (=>
                                                                     cmp5$2_0
                                                                     (let
                                                                        ((retval.0$2_0 0))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           false)))))))))))))))))))))))))
(assert
   (forall
      ((p1$1_0_old Int)
       (p2$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s1$2_0_old Int)
       (s2$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV p1$1_0_old p2$1_0_old HEAP$1_old s1$2_0_old s2$2_0_old HEAP$2_old)
         (let
            ((p1$1_0 p1$1_0_old))
            (let
               ((p2$1_0 p2$1_0_old)
                (HEAP$1 HEAP$1_old)
                (s1.0$1_0 p1$1_0))
               (let
                  ((s2.0$1_0 p2$1_0)
                   (incdec.ptr$1_0 (+ s1.0$1_0 1))
                   (_$1_0 (select HEAP$1 s1.0$1_0)))
                  (let
                     ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                      (_$1_1 (select HEAP$1 s2.0$1_0))
                      (conv$1_0 _$1_0))
                     (let
                        ((cmp$1_0 (= conv$1_0 0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((conv5$1_0 _$1_0)
                               (conv6$1_0 _$1_1))
                              (let
                                 ((cmp7$1_0 (= conv5$1_0 conv6$1_0)))
                                 (=>
                                    cmp7$1_0
                                    (let
                                       ((s1$2_0 s1$2_0_old)
                                        (s2$2_0 s2$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (s2.addr.0$2_0 s2$2_0)
                                           (s1.addr.0$2_0 s1$2_0))
                                          (let
                                             ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                             (let
                                                ((conv$2_0 _$2_0)
                                                 (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                                 (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                                (let
                                                   ((conv1$2_0 _$2_1))
                                                   (let
                                                      ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                      (=>
                                                         (not cmp$2_0)
                                                         (let
                                                            ((_$2_3 (select HEAP$2 s1.addr.0$2_0)))
                                                            (let
                                                               ((conv7$2_0 _$2_3)
                                                                (incdec.ptr8$2_0 (+ incdec.ptr$2_0 (- 1))))
                                                               (let
                                                                  ((_$2_4 (select HEAP$2 incdec.ptr8$2_0)))
                                                                  (let
                                                                     ((conv9$2_0 _$2_4))
                                                                     (let
                                                                        ((sub$2_0 (- conv7$2_0 conv9$2_0)))
                                                                        (let
                                                                           ((retval.0$2_0 sub$2_0))
                                                                           (let
                                                                              ((result$2 retval.0$2_0)
                                                                               (HEAP$2_res HEAP$2))
                                                                              false))))))))))))))))))))))))))
(assert
   (forall
      ((p1$1_0_old Int)
       (p2$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s1$2_0_old Int)
       (s2$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV p1$1_0_old p2$1_0_old HEAP$1_old s1$2_0_old s2$2_0_old HEAP$2_old)
         (let
            ((p1$1_0 p1$1_0_old))
            (let
               ((p2$1_0 p2$1_0_old)
                (HEAP$1 HEAP$1_old)
                (s1.0$1_0 p1$1_0))
               (let
                  ((s2.0$1_0 p2$1_0)
                   (incdec.ptr$1_0 (+ s1.0$1_0 1))
                   (_$1_0 (select HEAP$1 s1.0$1_0)))
                  (let
                     ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                      (_$1_1 (select HEAP$1 s2.0$1_0))
                      (conv$1_0 _$1_0))
                     (let
                        ((cmp$1_0 (= conv$1_0 0)))
                        (=>
                           cmp$1_0
                           (let
                              ((conv9$1_0 _$1_0)
                               (conv10$1_0 _$1_1))
                              (let
                                 ((sub11$1_0 (- conv9$1_0 conv10$1_0)))
                                 (let
                                    ((result$1 sub11$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (s1$2_0 s1$2_0_old)
                                     (s2$2_0 s2$2_0_old))
                                    (let
                                       ((HEAP$2 HEAP$2_old)
                                        (s2.addr.0$2_0 s2$2_0)
                                        (s1.addr.0$2_0 s1$2_0))
                                       (let
                                          ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                          (let
                                             ((conv$2_0 _$2_0)
                                              (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                              (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                             (let
                                                ((conv1$2_0 _$2_1))
                                                (let
                                                   ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                   (=>
                                                      cmp$2_0
                                                      (let
                                                         ((incdec.ptr3$2_0 (+ s1.addr.0$2_0 1))
                                                          (_$2_2 (select HEAP$2 s1.addr.0$2_0)))
                                                         (let
                                                            ((conv4$2_0 _$2_2))
                                                            (let
                                                               ((cmp5$2_0 (= conv4$2_0 0)))
                                                               (=>
                                                                  cmp5$2_0
                                                                  (let
                                                                     ((retval.0$2_0 0))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((p1$1_0_old Int)
       (p2$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s1$2_0_old Int)
       (s2$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV p1$1_0_old p2$1_0_old HEAP$1_old s1$2_0_old s2$2_0_old HEAP$2_old)
         (let
            ((p1$1_0 p1$1_0_old))
            (let
               ((p2$1_0 p2$1_0_old)
                (HEAP$1 HEAP$1_old)
                (s1.0$1_0 p1$1_0))
               (let
                  ((s2.0$1_0 p2$1_0)
                   (incdec.ptr$1_0 (+ s1.0$1_0 1))
                   (_$1_0 (select HEAP$1 s1.0$1_0)))
                  (let
                     ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                      (_$1_1 (select HEAP$1 s2.0$1_0))
                      (conv$1_0 _$1_0))
                     (let
                        ((cmp$1_0 (= conv$1_0 0)))
                        (=>
                           cmp$1_0
                           (let
                              ((conv9$1_0 _$1_0)
                               (conv10$1_0 _$1_1))
                              (let
                                 ((sub11$1_0 (- conv9$1_0 conv10$1_0)))
                                 (let
                                    ((result$1 sub11$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (s1$2_0 s1$2_0_old)
                                     (s2$2_0 s2$2_0_old))
                                    (let
                                       ((HEAP$2 HEAP$2_old)
                                        (s2.addr.0$2_0 s2$2_0)
                                        (s1.addr.0$2_0 s1$2_0))
                                       (let
                                          ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                          (let
                                             ((conv$2_0 _$2_0)
                                              (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                              (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                             (let
                                                ((conv1$2_0 _$2_1))
                                                (let
                                                   ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                   (=>
                                                      (not cmp$2_0)
                                                      (let
                                                         ((_$2_3 (select HEAP$2 s1.addr.0$2_0)))
                                                         (let
                                                            ((conv7$2_0 _$2_3)
                                                             (incdec.ptr8$2_0 (+ incdec.ptr$2_0 (- 1))))
                                                            (let
                                                               ((_$2_4 (select HEAP$2 incdec.ptr8$2_0)))
                                                               (let
                                                                  ((conv9$2_0 _$2_4))
                                                                  (let
                                                                     ((sub$2_0 (- conv7$2_0 conv9$2_0)))
                                                                     (let
                                                                        ((retval.0$2_0 sub$2_0))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((p1$1_0_old Int)
       (p2$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s1$2_0_old Int)
       (s2$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV p1$1_0_old p2$1_0_old HEAP$1_old s1$2_0_old s2$2_0_old HEAP$2_old)
         (let
            ((p1$1_0 p1$1_0_old))
            (let
               ((p2$1_0 p2$1_0_old)
                (HEAP$1 HEAP$1_old)
                (s1.0$1_0 p1$1_0))
               (let
                  ((s2.0$1_0 p2$1_0)
                   (incdec.ptr$1_0 (+ s1.0$1_0 1))
                   (_$1_0 (select HEAP$1 s1.0$1_0)))
                  (let
                     ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                      (_$1_1 (select HEAP$1 s2.0$1_0))
                      (conv$1_0 _$1_0))
                     (let
                        ((cmp$1_0 (= conv$1_0 0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((conv5$1_0 _$1_0)
                               (conv6$1_0 _$1_1))
                              (let
                                 ((cmp7$1_0 (= conv5$1_0 conv6$1_0)))
                                 (=>
                                    (not cmp7$1_0)
                                    (let
                                       ((conv9$1_0 _$1_0)
                                        (conv10$1_0 _$1_1))
                                       (let
                                          ((sub11$1_0 (- conv9$1_0 conv10$1_0)))
                                          (let
                                             ((result$1 sub11$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (s1$2_0 s1$2_0_old)
                                              (s2$2_0 s2$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (s2.addr.0$2_0 s2$2_0)
                                                 (s1.addr.0$2_0 s1$2_0))
                                                (let
                                                   ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                                   (let
                                                      ((conv$2_0 _$2_0)
                                                       (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                                       (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                                      (let
                                                         ((conv1$2_0 _$2_1))
                                                         (let
                                                            ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                            (=>
                                                               cmp$2_0
                                                               (let
                                                                  ((incdec.ptr3$2_0 (+ s1.addr.0$2_0 1))
                                                                   (_$2_2 (select HEAP$2 s1.addr.0$2_0)))
                                                                  (let
                                                                     ((conv4$2_0 _$2_2))
                                                                     (let
                                                                        ((cmp5$2_0 (= conv4$2_0 0)))
                                                                        (=>
                                                                           cmp5$2_0
                                                                           (let
                                                                              ((retval.0$2_0 0))
                                                                              (let
                                                                                 ((result$2 retval.0$2_0)
                                                                                  (HEAP$2_res HEAP$2))
                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))
(assert
   (forall
      ((p1$1_0_old Int)
       (p2$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s1$2_0_old Int)
       (s2$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV p1$1_0_old p2$1_0_old HEAP$1_old s1$2_0_old s2$2_0_old HEAP$2_old)
         (let
            ((p1$1_0 p1$1_0_old))
            (let
               ((p2$1_0 p2$1_0_old)
                (HEAP$1 HEAP$1_old)
                (s1.0$1_0 p1$1_0))
               (let
                  ((s2.0$1_0 p2$1_0)
                   (incdec.ptr$1_0 (+ s1.0$1_0 1))
                   (_$1_0 (select HEAP$1 s1.0$1_0)))
                  (let
                     ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                      (_$1_1 (select HEAP$1 s2.0$1_0))
                      (conv$1_0 _$1_0))
                     (let
                        ((cmp$1_0 (= conv$1_0 0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((conv5$1_0 _$1_0)
                               (conv6$1_0 _$1_1))
                              (let
                                 ((cmp7$1_0 (= conv5$1_0 conv6$1_0)))
                                 (=>
                                    (not cmp7$1_0)
                                    (let
                                       ((conv9$1_0 _$1_0)
                                        (conv10$1_0 _$1_1))
                                       (let
                                          ((sub11$1_0 (- conv9$1_0 conv10$1_0)))
                                          (let
                                             ((result$1 sub11$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (s1$2_0 s1$2_0_old)
                                              (s2$2_0 s2$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (s2.addr.0$2_0 s2$2_0)
                                                 (s1.addr.0$2_0 s1$2_0))
                                                (let
                                                   ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                                   (let
                                                      ((conv$2_0 _$2_0)
                                                       (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                                       (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                                      (let
                                                         ((conv1$2_0 _$2_1))
                                                         (let
                                                            ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                            (=>
                                                               (not cmp$2_0)
                                                               (let
                                                                  ((_$2_3 (select HEAP$2 s1.addr.0$2_0)))
                                                                  (let
                                                                     ((conv7$2_0 _$2_3)
                                                                      (incdec.ptr8$2_0 (+ incdec.ptr$2_0 (- 1))))
                                                                     (let
                                                                        ((_$2_4 (select HEAP$2 incdec.ptr8$2_0)))
                                                                        (let
                                                                           ((conv9$2_0 _$2_4))
                                                                           (let
                                                                              ((sub$2_0 (- conv7$2_0 conv9$2_0)))
                                                                              (let
                                                                                 ((retval.0$2_0 sub$2_0))
                                                                                 (let
                                                                                    ((result$2 retval.0$2_0)
                                                                                     (HEAP$2_res HEAP$2))
                                                                                    (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((p1$1_0_old Int)
       (p2$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s1$2_0_old Int)
       (s2$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV p1$1_0_old p2$1_0_old HEAP$1_old s1$2_0_old s2$2_0_old HEAP$2_old)
         (let
            ((p1$1_0 p1$1_0_old))
            (let
               ((p2$1_0 p2$1_0_old)
                (HEAP$1 HEAP$1_old)
                (s1.0$1_0 p1$1_0))
               (let
                  ((s2.0$1_0 p2$1_0)
                   (incdec.ptr$1_0 (+ s1.0$1_0 1))
                   (_$1_0 (select HEAP$1 s1.0$1_0)))
                  (let
                     ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                      (_$1_1 (select HEAP$1 s2.0$1_0))
                      (conv$1_0 _$1_0))
                     (let
                        ((cmp$1_0 (= conv$1_0 0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((conv5$1_0 _$1_0)
                               (conv6$1_0 _$1_1))
                              (let
                                 ((cmp7$1_0 (= conv5$1_0 conv6$1_0)))
                                 (=>
                                    cmp7$1_0
                                    (let
                                       ((s1$2_0 s1$2_0_old)
                                        (s2$2_0 s2$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (s2.addr.0$2_0 s2$2_0)
                                           (s1.addr.0$2_0 s1$2_0))
                                          (let
                                             ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                             (let
                                                ((conv$2_0 _$2_0)
                                                 (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                                 (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                                (let
                                                   ((conv1$2_0 _$2_1))
                                                   (let
                                                      ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((incdec.ptr3$2_0 (+ s1.addr.0$2_0 1))
                                                             (_$2_2 (select HEAP$2 s1.addr.0$2_0)))
                                                            (let
                                                               ((conv4$2_0 _$2_2))
                                                               (let
                                                                  ((cmp5$2_0 (= conv4$2_0 0)))
                                                                  (=>
                                                                     (not cmp5$2_0)
                                                                     (forall
                                                                        ((i1 Int)
                                                                         (i2 Int))
                                                                        (INV_MAIN_42 _$1_0 _$1_1 incdec.ptr$1_0 incdec.ptr1$1_0 i1 (select HEAP$1 i1) incdec.ptr$2_0 incdec.ptr3$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))
(assert
   (forall
      ((_$1_0_old Int)
       (_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (incdec.ptr$2_0_old Int)
       (incdec.ptr3$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 _$1_0_old _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old i1_old (select HEAP$1_old i1_old) incdec.ptr$2_0_old incdec.ptr3$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((_$1_0 _$1_0_old)
             (_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((s1.0$1_0 incdec.ptr$1_0))
                  (let
                     ((s2.0$1_0 incdec.ptr1$1_0)
                      (incdec.ptr$1_0 (+ s1.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.0$1_0))
                         (conv$1_0 _$1_0))
                        (let
                           ((cmp$1_0 (= conv$1_0 0)))
                           (=>
                              cmp$1_0
                              (let
                                 ((conv9$1_0 _$1_0)
                                  (conv10$1_0 _$1_1))
                                 (let
                                    ((sub11$1_0 (- conv9$1_0 conv10$1_0)))
                                    (let
                                       ((result$1 sub11$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                        (incdec.ptr3$2_0 incdec.ptr3$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (s2.addr.0$2_0 incdec.ptr$2_0)
                                           (s1.addr.0$2_0 incdec.ptr3$2_0))
                                          (let
                                             ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                             (let
                                                ((conv$2_0 _$2_0)
                                                 (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                                 (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                                (let
                                                   ((conv1$2_0 _$2_1))
                                                   (let
                                                      ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((incdec.ptr3$2_0 (+ s1.addr.0$2_0 1))
                                                             (_$2_2 (select HEAP$2 s1.addr.0$2_0)))
                                                            (let
                                                               ((conv4$2_0 _$2_2))
                                                               (let
                                                                  ((cmp5$2_0 (= conv4$2_0 0)))
                                                                  (=>
                                                                     cmp5$2_0
                                                                     (let
                                                                        ((retval.0$2_0 0))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((_$1_0_old Int)
       (_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (incdec.ptr$2_0_old Int)
       (incdec.ptr3$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 _$1_0_old _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old i1_old (select HEAP$1_old i1_old) incdec.ptr$2_0_old incdec.ptr3$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((_$1_0 _$1_0_old)
             (_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((s1.0$1_0 incdec.ptr$1_0))
                  (let
                     ((s2.0$1_0 incdec.ptr1$1_0)
                      (incdec.ptr$1_0 (+ s1.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.0$1_0))
                         (conv$1_0 _$1_0))
                        (let
                           ((cmp$1_0 (= conv$1_0 0)))
                           (=>
                              cmp$1_0
                              (let
                                 ((conv9$1_0 _$1_0)
                                  (conv10$1_0 _$1_1))
                                 (let
                                    ((sub11$1_0 (- conv9$1_0 conv10$1_0)))
                                    (let
                                       ((result$1 sub11$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                        (incdec.ptr3$2_0 incdec.ptr3$2_0_old))
                                       (let
                                          ((HEAP$2 HEAP$2_old)
                                           (s2.addr.0$2_0 incdec.ptr$2_0)
                                           (s1.addr.0$2_0 incdec.ptr3$2_0))
                                          (let
                                             ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                             (let
                                                ((conv$2_0 _$2_0)
                                                 (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                                 (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                                (let
                                                   ((conv1$2_0 _$2_1))
                                                   (let
                                                      ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                      (=>
                                                         (not cmp$2_0)
                                                         (let
                                                            ((_$2_3 (select HEAP$2 s1.addr.0$2_0)))
                                                            (let
                                                               ((conv7$2_0 _$2_3)
                                                                (incdec.ptr8$2_0 (+ incdec.ptr$2_0 (- 1))))
                                                               (let
                                                                  ((_$2_4 (select HEAP$2 incdec.ptr8$2_0)))
                                                                  (let
                                                                     ((conv9$2_0 _$2_4))
                                                                     (let
                                                                        ((sub$2_0 (- conv7$2_0 conv9$2_0)))
                                                                        (let
                                                                           ((retval.0$2_0 sub$2_0))
                                                                           (let
                                                                              ((result$2 retval.0$2_0)
                                                                               (HEAP$2_res HEAP$2))
                                                                              (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))
(assert
   (forall
      ((_$1_0_old Int)
       (_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (incdec.ptr$2_0_old Int)
       (incdec.ptr3$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 _$1_0_old _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old i1_old (select HEAP$1_old i1_old) incdec.ptr$2_0_old incdec.ptr3$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((_$1_0 _$1_0_old)
             (_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((s1.0$1_0 incdec.ptr$1_0))
                  (let
                     ((s2.0$1_0 incdec.ptr1$1_0)
                      (incdec.ptr$1_0 (+ s1.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.0$1_0))
                         (conv$1_0 _$1_0))
                        (let
                           ((cmp$1_0 (= conv$1_0 0)))
                           (=>
                              (not cmp$1_0)
                              (let
                                 ((conv5$1_0 _$1_0)
                                  (conv6$1_0 _$1_1))
                                 (let
                                    ((cmp7$1_0 (= conv5$1_0 conv6$1_0)))
                                    (=>
                                       (not cmp7$1_0)
                                       (let
                                          ((conv9$1_0 _$1_0)
                                           (conv10$1_0 _$1_1))
                                          (let
                                             ((sub11$1_0 (- conv9$1_0 conv10$1_0)))
                                             (let
                                                ((result$1 sub11$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                 (incdec.ptr3$2_0 incdec.ptr3$2_0_old))
                                                (let
                                                   ((HEAP$2 HEAP$2_old)
                                                    (s2.addr.0$2_0 incdec.ptr$2_0)
                                                    (s1.addr.0$2_0 incdec.ptr3$2_0))
                                                   (let
                                                      ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                                      (let
                                                         ((conv$2_0 _$2_0)
                                                          (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                                          (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                                         (let
                                                            ((conv1$2_0 _$2_1))
                                                            (let
                                                               ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                               (=>
                                                                  cmp$2_0
                                                                  (let
                                                                     ((incdec.ptr3$2_0 (+ s1.addr.0$2_0 1))
                                                                      (_$2_2 (select HEAP$2 s1.addr.0$2_0)))
                                                                     (let
                                                                        ((conv4$2_0 _$2_2))
                                                                        (let
                                                                           ((cmp5$2_0 (= conv4$2_0 0)))
                                                                           (=>
                                                                              cmp5$2_0
                                                                              (let
                                                                                 ((retval.0$2_0 0))
                                                                                 (let
                                                                                    ((result$2 retval.0$2_0)
                                                                                     (HEAP$2_res HEAP$2))
                                                                                    (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((_$1_0_old Int)
       (_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (incdec.ptr$2_0_old Int)
       (incdec.ptr3$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 _$1_0_old _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old i1_old (select HEAP$1_old i1_old) incdec.ptr$2_0_old incdec.ptr3$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((_$1_0 _$1_0_old)
             (_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((s1.0$1_0 incdec.ptr$1_0))
                  (let
                     ((s2.0$1_0 incdec.ptr1$1_0)
                      (incdec.ptr$1_0 (+ s1.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.0$1_0))
                         (conv$1_0 _$1_0))
                        (let
                           ((cmp$1_0 (= conv$1_0 0)))
                           (=>
                              (not cmp$1_0)
                              (let
                                 ((conv5$1_0 _$1_0)
                                  (conv6$1_0 _$1_1))
                                 (let
                                    ((cmp7$1_0 (= conv5$1_0 conv6$1_0)))
                                    (=>
                                       (not cmp7$1_0)
                                       (let
                                          ((conv9$1_0 _$1_0)
                                           (conv10$1_0 _$1_1))
                                          (let
                                             ((sub11$1_0 (- conv9$1_0 conv10$1_0)))
                                             (let
                                                ((result$1 sub11$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (incdec.ptr$2_0 incdec.ptr$2_0_old)
                                                 (incdec.ptr3$2_0 incdec.ptr3$2_0_old))
                                                (let
                                                   ((HEAP$2 HEAP$2_old)
                                                    (s2.addr.0$2_0 incdec.ptr$2_0)
                                                    (s1.addr.0$2_0 incdec.ptr3$2_0))
                                                   (let
                                                      ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                                      (let
                                                         ((conv$2_0 _$2_0)
                                                          (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                                          (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                                         (let
                                                            ((conv1$2_0 _$2_1))
                                                            (let
                                                               ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                               (=>
                                                                  (not cmp$2_0)
                                                                  (let
                                                                     ((_$2_3 (select HEAP$2 s1.addr.0$2_0)))
                                                                     (let
                                                                        ((conv7$2_0 _$2_3)
                                                                         (incdec.ptr8$2_0 (+ incdec.ptr$2_0 (- 1))))
                                                                        (let
                                                                           ((_$2_4 (select HEAP$2 incdec.ptr8$2_0)))
                                                                           (let
                                                                              ((conv9$2_0 _$2_4))
                                                                              (let
                                                                                 ((sub$2_0 (- conv7$2_0 conv9$2_0)))
                                                                                 (let
                                                                                    ((retval.0$2_0 sub$2_0))
                                                                                    (let
                                                                                       ((result$2 retval.0$2_0)
                                                                                        (HEAP$2_res HEAP$2))
                                                                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))
(assert
   (forall
      ((_$1_0_old Int)
       (_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (incdec.ptr$2_0_old Int)
       (incdec.ptr3$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 _$1_0_old _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old i1_old (select HEAP$1_old i1_old) incdec.ptr$2_0_old incdec.ptr3$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((_$1_0 _$1_0_old)
             (_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               (not tobool$1_0)
               (let
                  ((conv9$1_0 _$1_0)
                   (conv10$1_0 _$1_1))
                  (let
                     ((sub11$1_0 (- conv9$1_0 conv10$1_0)))
                     (let
                        ((result$1 sub11$1_0)
                         (HEAP$1_res HEAP$1)
                         (incdec.ptr$2_0 incdec.ptr$2_0_old)
                         (incdec.ptr3$2_0 incdec.ptr3$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (s2.addr.0$2_0 incdec.ptr$2_0)
                            (s1.addr.0$2_0 incdec.ptr3$2_0))
                           (let
                              ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                              (let
                                 ((conv$2_0 _$2_0)
                                  (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                  (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                 (let
                                    ((conv1$2_0 _$2_1))
                                    (let
                                       ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                       (=>
                                          cmp$2_0
                                          (let
                                             ((incdec.ptr3$2_0 (+ s1.addr.0$2_0 1))
                                              (_$2_2 (select HEAP$2 s1.addr.0$2_0)))
                                             (let
                                                ((conv4$2_0 _$2_2))
                                                (let
                                                   ((cmp5$2_0 (= conv4$2_0 0)))
                                                   (=>
                                                      cmp5$2_0
                                                      (let
                                                         ((retval.0$2_0 0))
                                                         (let
                                                            ((result$2 retval.0$2_0)
                                                             (HEAP$2_res HEAP$2))
                                                            (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))
(assert
   (forall
      ((_$1_0_old Int)
       (_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (incdec.ptr$2_0_old Int)
       (incdec.ptr3$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 _$1_0_old _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old i1_old (select HEAP$1_old i1_old) incdec.ptr$2_0_old incdec.ptr3$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((_$1_0 _$1_0_old)
             (_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               (not tobool$1_0)
               (let
                  ((conv9$1_0 _$1_0)
                   (conv10$1_0 _$1_1))
                  (let
                     ((sub11$1_0 (- conv9$1_0 conv10$1_0)))
                     (let
                        ((result$1 sub11$1_0)
                         (HEAP$1_res HEAP$1)
                         (incdec.ptr$2_0 incdec.ptr$2_0_old)
                         (incdec.ptr3$2_0 incdec.ptr3$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (s2.addr.0$2_0 incdec.ptr$2_0)
                            (s1.addr.0$2_0 incdec.ptr3$2_0))
                           (let
                              ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                              (let
                                 ((conv$2_0 _$2_0)
                                  (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                  (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                 (let
                                    ((conv1$2_0 _$2_1))
                                    (let
                                       ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                       (=>
                                          (not cmp$2_0)
                                          (let
                                             ((_$2_3 (select HEAP$2 s1.addr.0$2_0)))
                                             (let
                                                ((conv7$2_0 _$2_3)
                                                 (incdec.ptr8$2_0 (+ incdec.ptr$2_0 (- 1))))
                                                (let
                                                   ((_$2_4 (select HEAP$2 incdec.ptr8$2_0)))
                                                   (let
                                                      ((conv9$2_0 _$2_4))
                                                      (let
                                                         ((sub$2_0 (- conv7$2_0 conv9$2_0)))
                                                         (let
                                                            ((retval.0$2_0 sub$2_0))
                                                            (let
                                                               ((result$2 retval.0$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((_$1_0_old Int)
       (_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (incdec.ptr$2_0_old Int)
       (incdec.ptr3$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 _$1_0_old _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old i1_old (select HEAP$1_old i1_old) incdec.ptr$2_0_old incdec.ptr3$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((_$1_0 _$1_0_old)
             (_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((s1.0$1_0 incdec.ptr$1_0))
                  (let
                     ((s2.0$1_0 incdec.ptr1$1_0)
                      (incdec.ptr$1_0 (+ s1.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.0$1_0))
                         (conv$1_0 _$1_0))
                        (let
                           ((cmp$1_0 (= conv$1_0 0)))
                           (=>
                              (not cmp$1_0)
                              (let
                                 ((conv5$1_0 _$1_0)
                                  (conv6$1_0 _$1_1))
                                 (let
                                    ((cmp7$1_0 (= conv5$1_0 conv6$1_0)))
                                    (=>
                                       cmp7$1_0
                                       (let
                                          ((incdec.ptr$2_0 incdec.ptr$2_0_old)
                                           (incdec.ptr3$2_0 incdec.ptr3$2_0_old))
                                          (let
                                             ((HEAP$2 HEAP$2_old)
                                              (s2.addr.0$2_0 incdec.ptr$2_0)
                                              (s1.addr.0$2_0 incdec.ptr3$2_0))
                                             (let
                                                ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                                (let
                                                   ((conv$2_0 _$2_0)
                                                    (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                                    (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                                   (let
                                                      ((conv1$2_0 _$2_1))
                                                      (let
                                                         ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                         (=>
                                                            cmp$2_0
                                                            (let
                                                               ((incdec.ptr3$2_0 (+ s1.addr.0$2_0 1))
                                                                (_$2_2 (select HEAP$2 s1.addr.0$2_0)))
                                                               (let
                                                                  ((conv4$2_0 _$2_2))
                                                                  (let
                                                                     ((cmp5$2_0 (= conv4$2_0 0)))
                                                                     (=>
                                                                        (not cmp5$2_0)
                                                                        (forall
                                                                           ((i1 Int)
                                                                            (i2 Int))
                                                                           (INV_MAIN_42 _$1_0 _$1_1 incdec.ptr$1_0 incdec.ptr1$1_0 i1 (select HEAP$1 i1) incdec.ptr$2_0 incdec.ptr3$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))
(assert
   (forall
      ((_$1_0_old Int)
       (_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (incdec.ptr$2_0_old Int)
       (incdec.ptr3$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 _$1_0_old _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old i1_old (select HEAP$1_old i1_old) incdec.ptr$2_0_old incdec.ptr3$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((_$1_0 _$1_0_old)
             (_$1_1 _$1_1_old)
             (incdec.ptr$1_0 incdec.ptr$1_0_old)
             (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((s1.0$1_0 incdec.ptr$1_0))
                  (let
                     ((s2.0$1_0 incdec.ptr1$1_0)
                      (incdec.ptr$1_0 (+ s1.0$1_0 1))
                      (_$1_0 (select HEAP$1 s1.0$1_0)))
                     (let
                        ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                         (_$1_1 (select HEAP$1 s2.0$1_0))
                         (conv$1_0 _$1_0))
                        (let
                           ((cmp$1_0 (= conv$1_0 0)))
                           (=>
                              (not cmp$1_0)
                              (let
                                 ((conv5$1_0 _$1_0)
                                  (conv6$1_0 _$1_1))
                                 (let
                                    ((cmp7$1_0 (= conv5$1_0 conv6$1_0)))
                                    (=>
                                       cmp7$1_0
                                       (=>
                                          (let
                                             ((incdec.ptr$2_0 incdec.ptr$2_0_old)
                                              (incdec.ptr3$2_0 incdec.ptr3$2_0_old))
                                             (let
                                                ((HEAP$2 HEAP$2_old)
                                                 (s2.addr.0$2_0 incdec.ptr$2_0)
                                                 (s1.addr.0$2_0 incdec.ptr3$2_0))
                                                (let
                                                   ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                                                   (let
                                                      ((conv$2_0 _$2_0)
                                                       (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                                                       (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                                                      (let
                                                         ((conv1$2_0 _$2_1))
                                                         (let
                                                            ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                                                            (=>
                                                               cmp$2_0
                                                               (let
                                                                  ((incdec.ptr3$2_0 (+ s1.addr.0$2_0 1))
                                                                   (_$2_2 (select HEAP$2 s1.addr.0$2_0)))
                                                                  (let
                                                                     ((conv4$2_0 _$2_2))
                                                                     (let
                                                                        ((cmp5$2_0 (= conv4$2_0 0)))
                                                                        (not (not cmp5$2_0))))))))))))
                                          (forall
                                             ((i1 Int)
                                              (i2_old Int))
                                             (INV_MAIN_42 _$1_0 _$1_1 incdec.ptr$1_0 incdec.ptr1$1_0 i1 (select HEAP$1 i1) incdec.ptr$2_0_old incdec.ptr3$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))))))
(assert
   (forall
      ((_$1_0_old Int)
       (_$1_1_old Int)
       (incdec.ptr$1_0_old Int)
       (incdec.ptr1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (incdec.ptr$2_0_old Int)
       (incdec.ptr3$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 _$1_0_old _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old i1_old (select HEAP$1_old i1_old) incdec.ptr$2_0_old incdec.ptr3$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((incdec.ptr$2_0 incdec.ptr$2_0_old)
             (incdec.ptr3$2_0 incdec.ptr3$2_0_old))
            (let
               ((HEAP$2 HEAP$2_old)
                (s2.addr.0$2_0 incdec.ptr$2_0)
                (s1.addr.0$2_0 incdec.ptr3$2_0))
               (let
                  ((_$2_0 (select HEAP$2 s1.addr.0$2_0)))
                  (let
                     ((conv$2_0 _$2_0)
                      (incdec.ptr$2_0 (+ s2.addr.0$2_0 1))
                      (_$2_1 (select HEAP$2 s2.addr.0$2_0)))
                     (let
                        ((conv1$2_0 _$2_1))
                        (let
                           ((cmp$2_0 (= conv$2_0 conv1$2_0)))
                           (=>
                              cmp$2_0
                              (let
                                 ((incdec.ptr3$2_0 (+ s1.addr.0$2_0 1))
                                  (_$2_2 (select HEAP$2 s1.addr.0$2_0)))
                                 (let
                                    ((conv4$2_0 _$2_2))
                                    (let
                                       ((cmp5$2_0 (= conv4$2_0 0)))
                                       (=>
                                          (not cmp5$2_0)
                                          (=>
                                             (let
                                                ((_$1_0 _$1_0_old)
                                                 (_$1_1 _$1_1_old)
                                                 (incdec.ptr$1_0 incdec.ptr$1_0_old)
                                                 (incdec.ptr1$1_0 incdec.ptr1$1_0_old)
                                                 (HEAP$1 HEAP$1_old)
                                                 (tobool$1_0 (distinct 1 0)))
                                                (=>
                                                   tobool$1_0
                                                   (let
                                                      ((s1.0$1_0 incdec.ptr$1_0))
                                                      (let
                                                         ((s2.0$1_0 incdec.ptr1$1_0)
                                                          (incdec.ptr$1_0 (+ s1.0$1_0 1))
                                                          (_$1_0 (select HEAP$1 s1.0$1_0)))
                                                         (let
                                                            ((incdec.ptr1$1_0 (+ s2.0$1_0 1))
                                                             (_$1_1 (select HEAP$1 s2.0$1_0))
                                                             (conv$1_0 _$1_0))
                                                            (let
                                                               ((cmp$1_0 (= conv$1_0 0)))
                                                               (=>
                                                                  (not cmp$1_0)
                                                                  (let
                                                                     ((conv5$1_0 _$1_0)
                                                                      (conv6$1_0 _$1_1))
                                                                     (let
                                                                        ((cmp7$1_0 (= conv5$1_0 conv6$1_0)))
                                                                        (not cmp7$1_0))))))))))
                                             (forall
                                                ((i1_old Int)
                                                 (i2 Int))
                                                (INV_MAIN_42 _$1_0_old _$1_1_old incdec.ptr$1_0_old incdec.ptr1$1_0_old i1_old (select HEAP$1_old i1_old) incdec.ptr$2_0 incdec.ptr3$2_0 i2 (select HEAP$2 i2))))))))))))))))))
(check-sat)
(get-model)
