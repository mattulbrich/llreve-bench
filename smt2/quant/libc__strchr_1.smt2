;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((s$1_0 Int)
    (c_in$1_0 Int)
    (HEAP$1 (Array Int Int))
    (t$2_0 Int)
    (c$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= s$1_0 t$2_0)
      (= c_in$1_0 c$2_0)
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
; :annot (INV_MAIN_42 conv$1_0 s.addr.0$1_0 HEAP$1 conv$2_0 t.addr.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_42
   (Int
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
      ((s$1_0_old Int)
       (c_in$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (t$2_0_old Int)
       (c$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old c_in$1_0_old HEAP$1_old t$2_0_old c$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old)
             (c_in$1_0 c_in$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (conv$1_0 c_in$1_0)
                (s.addr.0$1_0 s$1_0)
                (t$2_0 t$2_0_old)
                (c$2_0 c$2_0_old))
               (let
                  ((HEAP$2 HEAP$2_old)
                   (conv$2_0 c$2_0)
                   (t.addr.0$2_0 t$2_0))
                  (forall
                     ((i1 Int)
                      (i2 Int))
                     (INV_MAIN_42 conv$1_0 s.addr.0$1_0 i1 (select HEAP$1 i1) conv$2_0 t.addr.0$2_0 i2 (select HEAP$2 i2)))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           cmp$1_0
                           (let
                              ((retval.0$1_0 s.addr.0$1_0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (conv$2_0 conv$2_0_old)
                                  (t.addr.0$2_0 t.addr.0$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (tobool$2_0 (distinct 1 0)))
                                 (=>
                                    tobool$2_0
                                    (let
                                       ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                       (let
                                          ((conv1$2_0 _$2_0)
                                           (conv2$2_0 conv$2_0))
                                          (let
                                             ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                             (=>
                                                cmp$2_0
                                                (let
                                                   ((retval.0$2_0 t.addr.0$2_0))
                                                   (let
                                                      ((result$2 retval.0$2_0)
                                                       (HEAP$2_res HEAP$2))
                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           cmp$1_0
                           (let
                              ((retval.0$1_0 s.addr.0$1_0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (conv$2_0 conv$2_0_old)
                                  (t.addr.0$2_0 t.addr.0$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (tobool$2_0 (distinct 1 0)))
                                 (=>
                                    tobool$2_0
                                    (let
                                       ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                       (let
                                          ((conv1$2_0 _$2_0)
                                           (conv2$2_0 conv$2_0))
                                          (let
                                             ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                             (=>
                                                (not cmp$2_0)
                                                (let
                                                   ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                   (let
                                                      ((tobool4$2_0 (distinct _$2_1 0)))
                                                      (=>
                                                         tobool4$2_0
                                                         (let
                                                            ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                            (let
                                                               ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                               (let
                                                                  ((conv7$2_0 _$2_2)
                                                                   (conv8$2_0 conv$2_0))
                                                                  (let
                                                                     ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                     (=>
                                                                        cmp9$2_0
                                                                        (let
                                                                           ((retval.0$2_0 incdec.ptr$2_0))
                                                                           (let
                                                                              ((result$2 retval.0$2_0)
                                                                               (HEAP$2_res HEAP$2))
                                                                              (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           cmp$1_0
                           (let
                              ((retval.0$1_0 s.addr.0$1_0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (conv$2_0 conv$2_0_old)
                                  (t.addr.0$2_0 t.addr.0$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (tobool$2_0 (distinct 1 0)))
                                 (=>
                                    tobool$2_0
                                    (let
                                       ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                       (let
                                          ((conv1$2_0 _$2_0)
                                           (conv2$2_0 conv$2_0))
                                          (let
                                             ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                             (=>
                                                (not cmp$2_0)
                                                (let
                                                   ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                   (let
                                                      ((tobool4$2_0 (distinct _$2_1 0)))
                                                      (=>
                                                         tobool4$2_0
                                                         (let
                                                            ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                            (let
                                                               ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                               (let
                                                                  ((conv7$2_0 _$2_2)
                                                                   (conv8$2_0 conv$2_0))
                                                                  (let
                                                                     ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                     (=>
                                                                        (not cmp9$2_0)
                                                                        (let
                                                                           ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                           (let
                                                                              ((tobool13$2_0 (distinct _$2_3 0)))
                                                                              (=>
                                                                                 tobool13$2_0
                                                                                 (let
                                                                                    ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                    (let
                                                                                       ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                       (let
                                                                                          ((conv17$2_0 _$2_4)
                                                                                           (conv18$2_0 conv$2_0))
                                                                                          (let
                                                                                             ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                             (=>
                                                                                                cmp19$2_0
                                                                                                (let
                                                                                                   ((retval.0$2_0 incdec.ptr16$2_0))
                                                                                                   (let
                                                                                                      ((result$2 retval.0$2_0)
                                                                                                       (HEAP$2_res HEAP$2))
                                                                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           cmp$1_0
                           (let
                              ((retval.0$1_0 s.addr.0$1_0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (conv$2_0 conv$2_0_old)
                                  (t.addr.0$2_0 t.addr.0$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (tobool$2_0 (distinct 1 0)))
                                 (=>
                                    tobool$2_0
                                    (let
                                       ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                       (let
                                          ((conv1$2_0 _$2_0)
                                           (conv2$2_0 conv$2_0))
                                          (let
                                             ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                             (=>
                                                (not cmp$2_0)
                                                (let
                                                   ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                   (let
                                                      ((tobool4$2_0 (distinct _$2_1 0)))
                                                      (=>
                                                         tobool4$2_0
                                                         (let
                                                            ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                            (let
                                                               ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                               (let
                                                                  ((conv7$2_0 _$2_2)
                                                                   (conv8$2_0 conv$2_0))
                                                                  (let
                                                                     ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                     (=>
                                                                        (not cmp9$2_0)
                                                                        (let
                                                                           ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                           (let
                                                                              ((tobool13$2_0 (distinct _$2_3 0)))
                                                                              (=>
                                                                                 tobool13$2_0
                                                                                 (let
                                                                                    ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                    (let
                                                                                       ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                       (let
                                                                                          ((conv17$2_0 _$2_4)
                                                                                           (conv18$2_0 conv$2_0))
                                                                                          (let
                                                                                             ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                             (=>
                                                                                                (not cmp19$2_0)
                                                                                                (let
                                                                                                   ((_$2_5 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                   (let
                                                                                                      ((tobool23$2_0 (distinct _$2_5 0)))
                                                                                                      (=>
                                                                                                         (not tobool23$2_0)
                                                                                                         (let
                                                                                                            ((retval.0$2_0 0))
                                                                                                            (let
                                                                                                               ((result$2 retval.0$2_0)
                                                                                                                (HEAP$2_res HEAP$2))
                                                                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           cmp$1_0
                           (let
                              ((retval.0$1_0 s.addr.0$1_0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (conv$2_0 conv$2_0_old)
                                  (t.addr.0$2_0 t.addr.0$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (tobool$2_0 (distinct 1 0)))
                                 (=>
                                    tobool$2_0
                                    (let
                                       ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                       (let
                                          ((conv1$2_0 _$2_0)
                                           (conv2$2_0 conv$2_0))
                                          (let
                                             ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                             (=>
                                                (not cmp$2_0)
                                                (let
                                                   ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                   (let
                                                      ((tobool4$2_0 (distinct _$2_1 0)))
                                                      (=>
                                                         tobool4$2_0
                                                         (let
                                                            ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                            (let
                                                               ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                               (let
                                                                  ((conv7$2_0 _$2_2)
                                                                   (conv8$2_0 conv$2_0))
                                                                  (let
                                                                     ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                     (=>
                                                                        (not cmp9$2_0)
                                                                        (let
                                                                           ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                           (let
                                                                              ((tobool13$2_0 (distinct _$2_3 0)))
                                                                              (=>
                                                                                 (not tobool13$2_0)
                                                                                 (let
                                                                                    ((retval.0$2_0 0))
                                                                                    (let
                                                                                       ((result$2 retval.0$2_0)
                                                                                        (HEAP$2_res HEAP$2))
                                                                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           cmp$1_0
                           (let
                              ((retval.0$1_0 s.addr.0$1_0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (conv$2_0 conv$2_0_old)
                                  (t.addr.0$2_0 t.addr.0$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (tobool$2_0 (distinct 1 0)))
                                 (=>
                                    tobool$2_0
                                    (let
                                       ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                       (let
                                          ((conv1$2_0 _$2_0)
                                           (conv2$2_0 conv$2_0))
                                          (let
                                             ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                             (=>
                                                (not cmp$2_0)
                                                (let
                                                   ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                   (let
                                                      ((tobool4$2_0 (distinct _$2_1 0)))
                                                      (=>
                                                         (not tobool4$2_0)
                                                         (let
                                                            ((retval.0$2_0 0))
                                                            (let
                                                               ((result$2 retval.0$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           cmp$1_0
                           (let
                              ((retval.0$1_0 s.addr.0$1_0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (conv$2_0 conv$2_0_old)
                                  (t.addr.0$2_0 t.addr.0$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (tobool$2_0 (distinct 1 0)))
                                 (=>
                                    (not tobool$2_0)
                                    (let
                                       ((retval.0$2_0 t.addr.0$2_0))
                                       (let
                                          ((result$2 retval.0$2_0)
                                           (HEAP$2_res HEAP$2))
                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       cmp5$1_0
                                       (let
                                          ((retval.0$1_0 0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (conv$2_0 conv$2_0_old)
                                              (t.addr.0$2_0 t.addr.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (tobool$2_0 (distinct 1 0)))
                                             (=>
                                                tobool$2_0
                                                (let
                                                   ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                   (let
                                                      ((conv1$2_0 _$2_0)
                                                       (conv2$2_0 conv$2_0))
                                                      (let
                                                         ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                         (=>
                                                            cmp$2_0
                                                            (let
                                                               ((retval.0$2_0 t.addr.0$2_0))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       cmp5$1_0
                                       (let
                                          ((retval.0$1_0 0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (conv$2_0 conv$2_0_old)
                                              (t.addr.0$2_0 t.addr.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (tobool$2_0 (distinct 1 0)))
                                             (=>
                                                tobool$2_0
                                                (let
                                                   ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                   (let
                                                      ((conv1$2_0 _$2_0)
                                                       (conv2$2_0 conv$2_0))
                                                      (let
                                                         ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                         (=>
                                                            (not cmp$2_0)
                                                            (let
                                                               ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                               (let
                                                                  ((tobool4$2_0 (distinct _$2_1 0)))
                                                                  (=>
                                                                     tobool4$2_0
                                                                     (let
                                                                        ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                        (let
                                                                           ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                           (let
                                                                              ((conv7$2_0 _$2_2)
                                                                               (conv8$2_0 conv$2_0))
                                                                              (let
                                                                                 ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                 (=>
                                                                                    cmp9$2_0
                                                                                    (let
                                                                                       ((retval.0$2_0 incdec.ptr$2_0))
                                                                                       (let
                                                                                          ((result$2 retval.0$2_0)
                                                                                           (HEAP$2_res HEAP$2))
                                                                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       cmp5$1_0
                                       (let
                                          ((retval.0$1_0 0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (conv$2_0 conv$2_0_old)
                                              (t.addr.0$2_0 t.addr.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (tobool$2_0 (distinct 1 0)))
                                             (=>
                                                tobool$2_0
                                                (let
                                                   ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                   (let
                                                      ((conv1$2_0 _$2_0)
                                                       (conv2$2_0 conv$2_0))
                                                      (let
                                                         ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                         (=>
                                                            (not cmp$2_0)
                                                            (let
                                                               ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                               (let
                                                                  ((tobool4$2_0 (distinct _$2_1 0)))
                                                                  (=>
                                                                     tobool4$2_0
                                                                     (let
                                                                        ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                        (let
                                                                           ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                           (let
                                                                              ((conv7$2_0 _$2_2)
                                                                               (conv8$2_0 conv$2_0))
                                                                              (let
                                                                                 ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                 (=>
                                                                                    (not cmp9$2_0)
                                                                                    (let
                                                                                       ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                       (let
                                                                                          ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                          (=>
                                                                                             tobool13$2_0
                                                                                             (let
                                                                                                ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                (let
                                                                                                   ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                   (let
                                                                                                      ((conv17$2_0 _$2_4)
                                                                                                       (conv18$2_0 conv$2_0))
                                                                                                      (let
                                                                                                         ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                         (=>
                                                                                                            cmp19$2_0
                                                                                                            (let
                                                                                                               ((retval.0$2_0 incdec.ptr16$2_0))
                                                                                                               (let
                                                                                                                  ((result$2 retval.0$2_0)
                                                                                                                   (HEAP$2_res HEAP$2))
                                                                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       cmp5$1_0
                                       (let
                                          ((retval.0$1_0 0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (conv$2_0 conv$2_0_old)
                                              (t.addr.0$2_0 t.addr.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (tobool$2_0 (distinct 1 0)))
                                             (=>
                                                tobool$2_0
                                                (let
                                                   ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                   (let
                                                      ((conv1$2_0 _$2_0)
                                                       (conv2$2_0 conv$2_0))
                                                      (let
                                                         ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                         (=>
                                                            (not cmp$2_0)
                                                            (let
                                                               ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                               (let
                                                                  ((tobool4$2_0 (distinct _$2_1 0)))
                                                                  (=>
                                                                     tobool4$2_0
                                                                     (let
                                                                        ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                        (let
                                                                           ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                           (let
                                                                              ((conv7$2_0 _$2_2)
                                                                               (conv8$2_0 conv$2_0))
                                                                              (let
                                                                                 ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                 (=>
                                                                                    (not cmp9$2_0)
                                                                                    (let
                                                                                       ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                       (let
                                                                                          ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                          (=>
                                                                                             tobool13$2_0
                                                                                             (let
                                                                                                ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                (let
                                                                                                   ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                   (let
                                                                                                      ((conv17$2_0 _$2_4)
                                                                                                       (conv18$2_0 conv$2_0))
                                                                                                      (let
                                                                                                         ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                         (=>
                                                                                                            (not cmp19$2_0)
                                                                                                            (let
                                                                                                               ((_$2_5 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                               (let
                                                                                                                  ((tobool23$2_0 (distinct _$2_5 0)))
                                                                                                                  (=>
                                                                                                                     (not tobool23$2_0)
                                                                                                                     (let
                                                                                                                        ((retval.0$2_0 0))
                                                                                                                        (let
                                                                                                                           ((result$2 retval.0$2_0)
                                                                                                                            (HEAP$2_res HEAP$2))
                                                                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       cmp5$1_0
                                       (let
                                          ((retval.0$1_0 0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (conv$2_0 conv$2_0_old)
                                              (t.addr.0$2_0 t.addr.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (tobool$2_0 (distinct 1 0)))
                                             (=>
                                                tobool$2_0
                                                (let
                                                   ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                   (let
                                                      ((conv1$2_0 _$2_0)
                                                       (conv2$2_0 conv$2_0))
                                                      (let
                                                         ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                         (=>
                                                            (not cmp$2_0)
                                                            (let
                                                               ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                               (let
                                                                  ((tobool4$2_0 (distinct _$2_1 0)))
                                                                  (=>
                                                                     tobool4$2_0
                                                                     (let
                                                                        ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                        (let
                                                                           ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                           (let
                                                                              ((conv7$2_0 _$2_2)
                                                                               (conv8$2_0 conv$2_0))
                                                                              (let
                                                                                 ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                 (=>
                                                                                    (not cmp9$2_0)
                                                                                    (let
                                                                                       ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                       (let
                                                                                          ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                          (=>
                                                                                             (not tobool13$2_0)
                                                                                             (let
                                                                                                ((retval.0$2_0 0))
                                                                                                (let
                                                                                                   ((result$2 retval.0$2_0)
                                                                                                    (HEAP$2_res HEAP$2))
                                                                                                   (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       cmp5$1_0
                                       (let
                                          ((retval.0$1_0 0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (conv$2_0 conv$2_0_old)
                                              (t.addr.0$2_0 t.addr.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (tobool$2_0 (distinct 1 0)))
                                             (=>
                                                tobool$2_0
                                                (let
                                                   ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                   (let
                                                      ((conv1$2_0 _$2_0)
                                                       (conv2$2_0 conv$2_0))
                                                      (let
                                                         ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                         (=>
                                                            (not cmp$2_0)
                                                            (let
                                                               ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                               (let
                                                                  ((tobool4$2_0 (distinct _$2_1 0)))
                                                                  (=>
                                                                     (not tobool4$2_0)
                                                                     (let
                                                                        ((retval.0$2_0 0))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       cmp5$1_0
                                       (let
                                          ((retval.0$1_0 0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (conv$2_0 conv$2_0_old)
                                              (t.addr.0$2_0 t.addr.0$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (tobool$2_0 (distinct 1 0)))
                                             (=>
                                                (not tobool$2_0)
                                                (let
                                                   ((retval.0$2_0 t.addr.0$2_0))
                                                   (let
                                                      ((result$2 retval.0$2_0)
                                                       (HEAP$2_res HEAP$2))
                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      cmp11$1_0
                                                      (let
                                                         ((retval.0$1_0 incdec.ptr$1_0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (conv$2_0 conv$2_0_old)
                                                             (t.addr.0$2_0 t.addr.0$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (tobool$2_0 (distinct 1 0)))
                                                            (=>
                                                               tobool$2_0
                                                               (let
                                                                  ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                  (let
                                                                     ((conv1$2_0 _$2_0)
                                                                      (conv2$2_0 conv$2_0))
                                                                     (let
                                                                        ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                        (=>
                                                                           cmp$2_0
                                                                           (let
                                                                              ((retval.0$2_0 t.addr.0$2_0))
                                                                              (let
                                                                                 ((result$2 retval.0$2_0)
                                                                                  (HEAP$2_res HEAP$2))
                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      cmp11$1_0
                                                      (let
                                                         ((retval.0$1_0 incdec.ptr$1_0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (conv$2_0 conv$2_0_old)
                                                             (t.addr.0$2_0 t.addr.0$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (tobool$2_0 (distinct 1 0)))
                                                            (=>
                                                               tobool$2_0
                                                               (let
                                                                  ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                  (let
                                                                     ((conv1$2_0 _$2_0)
                                                                      (conv2$2_0 conv$2_0))
                                                                     (let
                                                                        ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                        (=>
                                                                           (not cmp$2_0)
                                                                           (let
                                                                              ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                              (let
                                                                                 ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                 (=>
                                                                                    tobool4$2_0
                                                                                    (let
                                                                                       ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                       (let
                                                                                          ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                          (let
                                                                                             ((conv7$2_0 _$2_2)
                                                                                              (conv8$2_0 conv$2_0))
                                                                                             (let
                                                                                                ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                (=>
                                                                                                   cmp9$2_0
                                                                                                   (let
                                                                                                      ((retval.0$2_0 incdec.ptr$2_0))
                                                                                                      (let
                                                                                                         ((result$2 retval.0$2_0)
                                                                                                          (HEAP$2_res HEAP$2))
                                                                                                         (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      cmp11$1_0
                                                      (let
                                                         ((retval.0$1_0 incdec.ptr$1_0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (conv$2_0 conv$2_0_old)
                                                             (t.addr.0$2_0 t.addr.0$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (tobool$2_0 (distinct 1 0)))
                                                            (=>
                                                               tobool$2_0
                                                               (let
                                                                  ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                  (let
                                                                     ((conv1$2_0 _$2_0)
                                                                      (conv2$2_0 conv$2_0))
                                                                     (let
                                                                        ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                        (=>
                                                                           (not cmp$2_0)
                                                                           (let
                                                                              ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                              (let
                                                                                 ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                 (=>
                                                                                    tobool4$2_0
                                                                                    (let
                                                                                       ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                       (let
                                                                                          ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                          (let
                                                                                             ((conv7$2_0 _$2_2)
                                                                                              (conv8$2_0 conv$2_0))
                                                                                             (let
                                                                                                ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                (=>
                                                                                                   (not cmp9$2_0)
                                                                                                   (let
                                                                                                      ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                      (let
                                                                                                         ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                         (=>
                                                                                                            tobool13$2_0
                                                                                                            (let
                                                                                                               ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                               (let
                                                                                                                  ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                  (let
                                                                                                                     ((conv17$2_0 _$2_4)
                                                                                                                      (conv18$2_0 conv$2_0))
                                                                                                                     (let
                                                                                                                        ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                        (=>
                                                                                                                           cmp19$2_0
                                                                                                                           (let
                                                                                                                              ((retval.0$2_0 incdec.ptr16$2_0))
                                                                                                                              (let
                                                                                                                                 ((result$2 retval.0$2_0)
                                                                                                                                  (HEAP$2_res HEAP$2))
                                                                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      cmp11$1_0
                                                      (let
                                                         ((retval.0$1_0 incdec.ptr$1_0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (conv$2_0 conv$2_0_old)
                                                             (t.addr.0$2_0 t.addr.0$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (tobool$2_0 (distinct 1 0)))
                                                            (=>
                                                               tobool$2_0
                                                               (let
                                                                  ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                  (let
                                                                     ((conv1$2_0 _$2_0)
                                                                      (conv2$2_0 conv$2_0))
                                                                     (let
                                                                        ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                        (=>
                                                                           (not cmp$2_0)
                                                                           (let
                                                                              ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                              (let
                                                                                 ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                 (=>
                                                                                    tobool4$2_0
                                                                                    (let
                                                                                       ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                       (let
                                                                                          ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                          (let
                                                                                             ((conv7$2_0 _$2_2)
                                                                                              (conv8$2_0 conv$2_0))
                                                                                             (let
                                                                                                ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                (=>
                                                                                                   (not cmp9$2_0)
                                                                                                   (let
                                                                                                      ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                      (let
                                                                                                         ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                         (=>
                                                                                                            tobool13$2_0
                                                                                                            (let
                                                                                                               ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                               (let
                                                                                                                  ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                  (let
                                                                                                                     ((conv17$2_0 _$2_4)
                                                                                                                      (conv18$2_0 conv$2_0))
                                                                                                                     (let
                                                                                                                        ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                        (=>
                                                                                                                           (not cmp19$2_0)
                                                                                                                           (let
                                                                                                                              ((_$2_5 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                              (let
                                                                                                                                 ((tobool23$2_0 (distinct _$2_5 0)))
                                                                                                                                 (=>
                                                                                                                                    (not tobool23$2_0)
                                                                                                                                    (let
                                                                                                                                       ((retval.0$2_0 0))
                                                                                                                                       (let
                                                                                                                                          ((result$2 retval.0$2_0)
                                                                                                                                           (HEAP$2_res HEAP$2))
                                                                                                                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      cmp11$1_0
                                                      (let
                                                         ((retval.0$1_0 incdec.ptr$1_0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (conv$2_0 conv$2_0_old)
                                                             (t.addr.0$2_0 t.addr.0$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (tobool$2_0 (distinct 1 0)))
                                                            (=>
                                                               tobool$2_0
                                                               (let
                                                                  ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                  (let
                                                                     ((conv1$2_0 _$2_0)
                                                                      (conv2$2_0 conv$2_0))
                                                                     (let
                                                                        ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                        (=>
                                                                           (not cmp$2_0)
                                                                           (let
                                                                              ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                              (let
                                                                                 ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                 (=>
                                                                                    tobool4$2_0
                                                                                    (let
                                                                                       ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                       (let
                                                                                          ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                          (let
                                                                                             ((conv7$2_0 _$2_2)
                                                                                              (conv8$2_0 conv$2_0))
                                                                                             (let
                                                                                                ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                (=>
                                                                                                   (not cmp9$2_0)
                                                                                                   (let
                                                                                                      ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                      (let
                                                                                                         ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                         (=>
                                                                                                            (not tobool13$2_0)
                                                                                                            (let
                                                                                                               ((retval.0$2_0 0))
                                                                                                               (let
                                                                                                                  ((result$2 retval.0$2_0)
                                                                                                                   (HEAP$2_res HEAP$2))
                                                                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      cmp11$1_0
                                                      (let
                                                         ((retval.0$1_0 incdec.ptr$1_0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (conv$2_0 conv$2_0_old)
                                                             (t.addr.0$2_0 t.addr.0$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (tobool$2_0 (distinct 1 0)))
                                                            (=>
                                                               tobool$2_0
                                                               (let
                                                                  ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                  (let
                                                                     ((conv1$2_0 _$2_0)
                                                                      (conv2$2_0 conv$2_0))
                                                                     (let
                                                                        ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                        (=>
                                                                           (not cmp$2_0)
                                                                           (let
                                                                              ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                              (let
                                                                                 ((tobool4$2_0 (distinct _$2_1 0)))
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
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      cmp11$1_0
                                                      (let
                                                         ((retval.0$1_0 incdec.ptr$1_0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (conv$2_0 conv$2_0_old)
                                                             (t.addr.0$2_0 t.addr.0$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (tobool$2_0 (distinct 1 0)))
                                                            (=>
                                                               (not tobool$2_0)
                                                               (let
                                                                  ((retval.0$2_0 t.addr.0$2_0))
                                                                  (let
                                                                     ((result$2 retval.0$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  cmp16$1_0
                                                                  (let
                                                                     ((retval.0$1_0 0))
                                                                     (let
                                                                        ((result$1 retval.0$1_0)
                                                                         (HEAP$1_res HEAP$1)
                                                                         (conv$2_0 conv$2_0_old)
                                                                         (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                         (HEAP$2 HEAP$2_old)
                                                                         (tobool$2_0 (distinct 1 0)))
                                                                        (=>
                                                                           tobool$2_0
                                                                           (let
                                                                              ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                              (let
                                                                                 ((conv1$2_0 _$2_0)
                                                                                  (conv2$2_0 conv$2_0))
                                                                                 (let
                                                                                    ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                    (=>
                                                                                       cmp$2_0
                                                                                       (let
                                                                                          ((retval.0$2_0 t.addr.0$2_0))
                                                                                          (let
                                                                                             ((result$2 retval.0$2_0)
                                                                                              (HEAP$2_res HEAP$2))
                                                                                             (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  cmp16$1_0
                                                                  (let
                                                                     ((retval.0$1_0 0))
                                                                     (let
                                                                        ((result$1 retval.0$1_0)
                                                                         (HEAP$1_res HEAP$1)
                                                                         (conv$2_0 conv$2_0_old)
                                                                         (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                         (HEAP$2 HEAP$2_old)
                                                                         (tobool$2_0 (distinct 1 0)))
                                                                        (=>
                                                                           tobool$2_0
                                                                           (let
                                                                              ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                              (let
                                                                                 ((conv1$2_0 _$2_0)
                                                                                  (conv2$2_0 conv$2_0))
                                                                                 (let
                                                                                    ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                    (=>
                                                                                       (not cmp$2_0)
                                                                                       (let
                                                                                          ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                          (let
                                                                                             ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                             (=>
                                                                                                tobool4$2_0
                                                                                                (let
                                                                                                   ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                   (let
                                                                                                      ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                      (let
                                                                                                         ((conv7$2_0 _$2_2)
                                                                                                          (conv8$2_0 conv$2_0))
                                                                                                         (let
                                                                                                            ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                            (=>
                                                                                                               cmp9$2_0
                                                                                                               (let
                                                                                                                  ((retval.0$2_0 incdec.ptr$2_0))
                                                                                                                  (let
                                                                                                                     ((result$2 retval.0$2_0)
                                                                                                                      (HEAP$2_res HEAP$2))
                                                                                                                     (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  cmp16$1_0
                                                                  (let
                                                                     ((retval.0$1_0 0))
                                                                     (let
                                                                        ((result$1 retval.0$1_0)
                                                                         (HEAP$1_res HEAP$1)
                                                                         (conv$2_0 conv$2_0_old)
                                                                         (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                         (HEAP$2 HEAP$2_old)
                                                                         (tobool$2_0 (distinct 1 0)))
                                                                        (=>
                                                                           tobool$2_0
                                                                           (let
                                                                              ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                              (let
                                                                                 ((conv1$2_0 _$2_0)
                                                                                  (conv2$2_0 conv$2_0))
                                                                                 (let
                                                                                    ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                    (=>
                                                                                       (not cmp$2_0)
                                                                                       (let
                                                                                          ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                          (let
                                                                                             ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                             (=>
                                                                                                tobool4$2_0
                                                                                                (let
                                                                                                   ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                   (let
                                                                                                      ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                      (let
                                                                                                         ((conv7$2_0 _$2_2)
                                                                                                          (conv8$2_0 conv$2_0))
                                                                                                         (let
                                                                                                            ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                            (=>
                                                                                                               (not cmp9$2_0)
                                                                                                               (let
                                                                                                                  ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                  (let
                                                                                                                     ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                     (=>
                                                                                                                        tobool13$2_0
                                                                                                                        (let
                                                                                                                           ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                                           (let
                                                                                                                              ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                              (let
                                                                                                                                 ((conv17$2_0 _$2_4)
                                                                                                                                  (conv18$2_0 conv$2_0))
                                                                                                                                 (let
                                                                                                                                    ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                                    (=>
                                                                                                                                       cmp19$2_0
                                                                                                                                       (let
                                                                                                                                          ((retval.0$2_0 incdec.ptr16$2_0))
                                                                                                                                          (let
                                                                                                                                             ((result$2 retval.0$2_0)
                                                                                                                                              (HEAP$2_res HEAP$2))
                                                                                                                                             (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  cmp16$1_0
                                                                  (let
                                                                     ((retval.0$1_0 0))
                                                                     (let
                                                                        ((result$1 retval.0$1_0)
                                                                         (HEAP$1_res HEAP$1)
                                                                         (conv$2_0 conv$2_0_old)
                                                                         (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                         (HEAP$2 HEAP$2_old)
                                                                         (tobool$2_0 (distinct 1 0)))
                                                                        (=>
                                                                           tobool$2_0
                                                                           (let
                                                                              ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                              (let
                                                                                 ((conv1$2_0 _$2_0)
                                                                                  (conv2$2_0 conv$2_0))
                                                                                 (let
                                                                                    ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                    (=>
                                                                                       (not cmp$2_0)
                                                                                       (let
                                                                                          ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                          (let
                                                                                             ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                             (=>
                                                                                                tobool4$2_0
                                                                                                (let
                                                                                                   ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                   (let
                                                                                                      ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                      (let
                                                                                                         ((conv7$2_0 _$2_2)
                                                                                                          (conv8$2_0 conv$2_0))
                                                                                                         (let
                                                                                                            ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                            (=>
                                                                                                               (not cmp9$2_0)
                                                                                                               (let
                                                                                                                  ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                  (let
                                                                                                                     ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                     (=>
                                                                                                                        tobool13$2_0
                                                                                                                        (let
                                                                                                                           ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                                           (let
                                                                                                                              ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                              (let
                                                                                                                                 ((conv17$2_0 _$2_4)
                                                                                                                                  (conv18$2_0 conv$2_0))
                                                                                                                                 (let
                                                                                                                                    ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                                    (=>
                                                                                                                                       (not cmp19$2_0)
                                                                                                                                       (let
                                                                                                                                          ((_$2_5 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                          (let
                                                                                                                                             ((tobool23$2_0 (distinct _$2_5 0)))
                                                                                                                                             (=>
                                                                                                                                                (not tobool23$2_0)
                                                                                                                                                (let
                                                                                                                                                   ((retval.0$2_0 0))
                                                                                                                                                   (let
                                                                                                                                                      ((result$2 retval.0$2_0)
                                                                                                                                                       (HEAP$2_res HEAP$2))
                                                                                                                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  cmp16$1_0
                                                                  (let
                                                                     ((retval.0$1_0 0))
                                                                     (let
                                                                        ((result$1 retval.0$1_0)
                                                                         (HEAP$1_res HEAP$1)
                                                                         (conv$2_0 conv$2_0_old)
                                                                         (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                         (HEAP$2 HEAP$2_old)
                                                                         (tobool$2_0 (distinct 1 0)))
                                                                        (=>
                                                                           tobool$2_0
                                                                           (let
                                                                              ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                              (let
                                                                                 ((conv1$2_0 _$2_0)
                                                                                  (conv2$2_0 conv$2_0))
                                                                                 (let
                                                                                    ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                    (=>
                                                                                       (not cmp$2_0)
                                                                                       (let
                                                                                          ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                          (let
                                                                                             ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                             (=>
                                                                                                tobool4$2_0
                                                                                                (let
                                                                                                   ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                   (let
                                                                                                      ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                      (let
                                                                                                         ((conv7$2_0 _$2_2)
                                                                                                          (conv8$2_0 conv$2_0))
                                                                                                         (let
                                                                                                            ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                            (=>
                                                                                                               (not cmp9$2_0)
                                                                                                               (let
                                                                                                                  ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                  (let
                                                                                                                     ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                     (=>
                                                                                                                        (not tobool13$2_0)
                                                                                                                        (let
                                                                                                                           ((retval.0$2_0 0))
                                                                                                                           (let
                                                                                                                              ((result$2 retval.0$2_0)
                                                                                                                               (HEAP$2_res HEAP$2))
                                                                                                                              (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  cmp16$1_0
                                                                  (let
                                                                     ((retval.0$1_0 0))
                                                                     (let
                                                                        ((result$1 retval.0$1_0)
                                                                         (HEAP$1_res HEAP$1)
                                                                         (conv$2_0 conv$2_0_old)
                                                                         (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                         (HEAP$2 HEAP$2_old)
                                                                         (tobool$2_0 (distinct 1 0)))
                                                                        (=>
                                                                           tobool$2_0
                                                                           (let
                                                                              ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                              (let
                                                                                 ((conv1$2_0 _$2_0)
                                                                                  (conv2$2_0 conv$2_0))
                                                                                 (let
                                                                                    ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                    (=>
                                                                                       (not cmp$2_0)
                                                                                       (let
                                                                                          ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                          (let
                                                                                             ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                             (=>
                                                                                                (not tobool4$2_0)
                                                                                                (let
                                                                                                   ((retval.0$2_0 0))
                                                                                                   (let
                                                                                                      ((result$2 retval.0$2_0)
                                                                                                       (HEAP$2_res HEAP$2))
                                                                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  cmp16$1_0
                                                                  (let
                                                                     ((retval.0$1_0 0))
                                                                     (let
                                                                        ((result$1 retval.0$1_0)
                                                                         (HEAP$1_res HEAP$1)
                                                                         (conv$2_0 conv$2_0_old)
                                                                         (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                         (HEAP$2 HEAP$2_old)
                                                                         (tobool$2_0 (distinct 1 0)))
                                                                        (=>
                                                                           (not tobool$2_0)
                                                                           (let
                                                                              ((retval.0$2_0 t.addr.0$2_0))
                                                                              (let
                                                                                 ((result$2 retval.0$2_0)
                                                                                  (HEAP$2_res HEAP$2))
                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 cmp24$1_0
                                                                                 (let
                                                                                    ((retval.0$1_0 incdec.ptr21$1_0))
                                                                                    (let
                                                                                       ((result$1 retval.0$1_0)
                                                                                        (HEAP$1_res HEAP$1)
                                                                                        (conv$2_0 conv$2_0_old)
                                                                                        (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                        (HEAP$2 HEAP$2_old)
                                                                                        (tobool$2_0 (distinct 1 0)))
                                                                                       (=>
                                                                                          tobool$2_0
                                                                                          (let
                                                                                             ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                             (let
                                                                                                ((conv1$2_0 _$2_0)
                                                                                                 (conv2$2_0 conv$2_0))
                                                                                                (let
                                                                                                   ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                   (=>
                                                                                                      cmp$2_0
                                                                                                      (let
                                                                                                         ((retval.0$2_0 t.addr.0$2_0))
                                                                                                         (let
                                                                                                            ((result$2 retval.0$2_0)
                                                                                                             (HEAP$2_res HEAP$2))
                                                                                                            (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 cmp24$1_0
                                                                                 (let
                                                                                    ((retval.0$1_0 incdec.ptr21$1_0))
                                                                                    (let
                                                                                       ((result$1 retval.0$1_0)
                                                                                        (HEAP$1_res HEAP$1)
                                                                                        (conv$2_0 conv$2_0_old)
                                                                                        (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                        (HEAP$2 HEAP$2_old)
                                                                                        (tobool$2_0 (distinct 1 0)))
                                                                                       (=>
                                                                                          tobool$2_0
                                                                                          (let
                                                                                             ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                             (let
                                                                                                ((conv1$2_0 _$2_0)
                                                                                                 (conv2$2_0 conv$2_0))
                                                                                                (let
                                                                                                   ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                   (=>
                                                                                                      (not cmp$2_0)
                                                                                                      (let
                                                                                                         ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                         (let
                                                                                                            ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                            (=>
                                                                                                               tobool4$2_0
                                                                                                               (let
                                                                                                                  ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                  (let
                                                                                                                     ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                     (let
                                                                                                                        ((conv7$2_0 _$2_2)
                                                                                                                         (conv8$2_0 conv$2_0))
                                                                                                                        (let
                                                                                                                           ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                           (=>
                                                                                                                              cmp9$2_0
                                                                                                                              (let
                                                                                                                                 ((retval.0$2_0 incdec.ptr$2_0))
                                                                                                                                 (let
                                                                                                                                    ((result$2 retval.0$2_0)
                                                                                                                                     (HEAP$2_res HEAP$2))
                                                                                                                                    (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 cmp24$1_0
                                                                                 (let
                                                                                    ((retval.0$1_0 incdec.ptr21$1_0))
                                                                                    (let
                                                                                       ((result$1 retval.0$1_0)
                                                                                        (HEAP$1_res HEAP$1)
                                                                                        (conv$2_0 conv$2_0_old)
                                                                                        (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                        (HEAP$2 HEAP$2_old)
                                                                                        (tobool$2_0 (distinct 1 0)))
                                                                                       (=>
                                                                                          tobool$2_0
                                                                                          (let
                                                                                             ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                             (let
                                                                                                ((conv1$2_0 _$2_0)
                                                                                                 (conv2$2_0 conv$2_0))
                                                                                                (let
                                                                                                   ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                   (=>
                                                                                                      (not cmp$2_0)
                                                                                                      (let
                                                                                                         ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                         (let
                                                                                                            ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                            (=>
                                                                                                               tobool4$2_0
                                                                                                               (let
                                                                                                                  ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                  (let
                                                                                                                     ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                     (let
                                                                                                                        ((conv7$2_0 _$2_2)
                                                                                                                         (conv8$2_0 conv$2_0))
                                                                                                                        (let
                                                                                                                           ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                           (=>
                                                                                                                              (not cmp9$2_0)
                                                                                                                              (let
                                                                                                                                 ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                 (let
                                                                                                                                    ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                    (=>
                                                                                                                                       tobool13$2_0
                                                                                                                                       (let
                                                                                                                                          ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                                                          (let
                                                                                                                                             ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                             (let
                                                                                                                                                ((conv17$2_0 _$2_4)
                                                                                                                                                 (conv18$2_0 conv$2_0))
                                                                                                                                                (let
                                                                                                                                                   ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                                                   (=>
                                                                                                                                                      cmp19$2_0
                                                                                                                                                      (let
                                                                                                                                                         ((retval.0$2_0 incdec.ptr16$2_0))
                                                                                                                                                         (let
                                                                                                                                                            ((result$2 retval.0$2_0)
                                                                                                                                                             (HEAP$2_res HEAP$2))
                                                                                                                                                            (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 cmp24$1_0
                                                                                 (let
                                                                                    ((retval.0$1_0 incdec.ptr21$1_0))
                                                                                    (let
                                                                                       ((result$1 retval.0$1_0)
                                                                                        (HEAP$1_res HEAP$1)
                                                                                        (conv$2_0 conv$2_0_old)
                                                                                        (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                        (HEAP$2 HEAP$2_old)
                                                                                        (tobool$2_0 (distinct 1 0)))
                                                                                       (=>
                                                                                          tobool$2_0
                                                                                          (let
                                                                                             ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                             (let
                                                                                                ((conv1$2_0 _$2_0)
                                                                                                 (conv2$2_0 conv$2_0))
                                                                                                (let
                                                                                                   ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                   (=>
                                                                                                      (not cmp$2_0)
                                                                                                      (let
                                                                                                         ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                         (let
                                                                                                            ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                            (=>
                                                                                                               tobool4$2_0
                                                                                                               (let
                                                                                                                  ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                  (let
                                                                                                                     ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                     (let
                                                                                                                        ((conv7$2_0 _$2_2)
                                                                                                                         (conv8$2_0 conv$2_0))
                                                                                                                        (let
                                                                                                                           ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                           (=>
                                                                                                                              (not cmp9$2_0)
                                                                                                                              (let
                                                                                                                                 ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                 (let
                                                                                                                                    ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                    (=>
                                                                                                                                       tobool13$2_0
                                                                                                                                       (let
                                                                                                                                          ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                                                          (let
                                                                                                                                             ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                             (let
                                                                                                                                                ((conv17$2_0 _$2_4)
                                                                                                                                                 (conv18$2_0 conv$2_0))
                                                                                                                                                (let
                                                                                                                                                   ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                                                   (=>
                                                                                                                                                      (not cmp19$2_0)
                                                                                                                                                      (let
                                                                                                                                                         ((_$2_5 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                         (let
                                                                                                                                                            ((tobool23$2_0 (distinct _$2_5 0)))
                                                                                                                                                            (=>
                                                                                                                                                               (not tobool23$2_0)
                                                                                                                                                               (let
                                                                                                                                                                  ((retval.0$2_0 0))
                                                                                                                                                                  (let
                                                                                                                                                                     ((result$2 retval.0$2_0)
                                                                                                                                                                      (HEAP$2_res HEAP$2))
                                                                                                                                                                     (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 cmp24$1_0
                                                                                 (let
                                                                                    ((retval.0$1_0 incdec.ptr21$1_0))
                                                                                    (let
                                                                                       ((result$1 retval.0$1_0)
                                                                                        (HEAP$1_res HEAP$1)
                                                                                        (conv$2_0 conv$2_0_old)
                                                                                        (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                        (HEAP$2 HEAP$2_old)
                                                                                        (tobool$2_0 (distinct 1 0)))
                                                                                       (=>
                                                                                          tobool$2_0
                                                                                          (let
                                                                                             ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                             (let
                                                                                                ((conv1$2_0 _$2_0)
                                                                                                 (conv2$2_0 conv$2_0))
                                                                                                (let
                                                                                                   ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                   (=>
                                                                                                      (not cmp$2_0)
                                                                                                      (let
                                                                                                         ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                         (let
                                                                                                            ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                            (=>
                                                                                                               tobool4$2_0
                                                                                                               (let
                                                                                                                  ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                  (let
                                                                                                                     ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                     (let
                                                                                                                        ((conv7$2_0 _$2_2)
                                                                                                                         (conv8$2_0 conv$2_0))
                                                                                                                        (let
                                                                                                                           ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                           (=>
                                                                                                                              (not cmp9$2_0)
                                                                                                                              (let
                                                                                                                                 ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                 (let
                                                                                                                                    ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                    (=>
                                                                                                                                       (not tobool13$2_0)
                                                                                                                                       (let
                                                                                                                                          ((retval.0$2_0 0))
                                                                                                                                          (let
                                                                                                                                             ((result$2 retval.0$2_0)
                                                                                                                                              (HEAP$2_res HEAP$2))
                                                                                                                                             (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 cmp24$1_0
                                                                                 (let
                                                                                    ((retval.0$1_0 incdec.ptr21$1_0))
                                                                                    (let
                                                                                       ((result$1 retval.0$1_0)
                                                                                        (HEAP$1_res HEAP$1)
                                                                                        (conv$2_0 conv$2_0_old)
                                                                                        (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                        (HEAP$2 HEAP$2_old)
                                                                                        (tobool$2_0 (distinct 1 0)))
                                                                                       (=>
                                                                                          tobool$2_0
                                                                                          (let
                                                                                             ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                             (let
                                                                                                ((conv1$2_0 _$2_0)
                                                                                                 (conv2$2_0 conv$2_0))
                                                                                                (let
                                                                                                   ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                   (=>
                                                                                                      (not cmp$2_0)
                                                                                                      (let
                                                                                                         ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                         (let
                                                                                                            ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                            (=>
                                                                                                               (not tobool4$2_0)
                                                                                                               (let
                                                                                                                  ((retval.0$2_0 0))
                                                                                                                  (let
                                                                                                                     ((result$2 retval.0$2_0)
                                                                                                                      (HEAP$2_res HEAP$2))
                                                                                                                     (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 cmp24$1_0
                                                                                 (let
                                                                                    ((retval.0$1_0 incdec.ptr21$1_0))
                                                                                    (let
                                                                                       ((result$1 retval.0$1_0)
                                                                                        (HEAP$1_res HEAP$1)
                                                                                        (conv$2_0 conv$2_0_old)
                                                                                        (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                        (HEAP$2 HEAP$2_old)
                                                                                        (tobool$2_0 (distinct 1 0)))
                                                                                       (=>
                                                                                          (not tobool$2_0)
                                                                                          (let
                                                                                             ((retval.0$2_0 t.addr.0$2_0))
                                                                                             (let
                                                                                                ((result$2 retval.0$2_0)
                                                                                                 (HEAP$2_res HEAP$2))
                                                                                                (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             cmp29$1_0
                                                                                             (let
                                                                                                ((retval.0$1_0 0))
                                                                                                (let
                                                                                                   ((result$1 retval.0$1_0)
                                                                                                    (HEAP$1_res HEAP$1)
                                                                                                    (conv$2_0 conv$2_0_old)
                                                                                                    (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                    (HEAP$2 HEAP$2_old)
                                                                                                    (tobool$2_0 (distinct 1 0)))
                                                                                                   (=>
                                                                                                      tobool$2_0
                                                                                                      (let
                                                                                                         ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                         (let
                                                                                                            ((conv1$2_0 _$2_0)
                                                                                                             (conv2$2_0 conv$2_0))
                                                                                                            (let
                                                                                                               ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                               (=>
                                                                                                                  cmp$2_0
                                                                                                                  (let
                                                                                                                     ((retval.0$2_0 t.addr.0$2_0))
                                                                                                                     (let
                                                                                                                        ((result$2 retval.0$2_0)
                                                                                                                         (HEAP$2_res HEAP$2))
                                                                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             cmp29$1_0
                                                                                             (let
                                                                                                ((retval.0$1_0 0))
                                                                                                (let
                                                                                                   ((result$1 retval.0$1_0)
                                                                                                    (HEAP$1_res HEAP$1)
                                                                                                    (conv$2_0 conv$2_0_old)
                                                                                                    (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                    (HEAP$2 HEAP$2_old)
                                                                                                    (tobool$2_0 (distinct 1 0)))
                                                                                                   (=>
                                                                                                      tobool$2_0
                                                                                                      (let
                                                                                                         ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                         (let
                                                                                                            ((conv1$2_0 _$2_0)
                                                                                                             (conv2$2_0 conv$2_0))
                                                                                                            (let
                                                                                                               ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                               (=>
                                                                                                                  (not cmp$2_0)
                                                                                                                  (let
                                                                                                                     ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                     (let
                                                                                                                        ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                        (=>
                                                                                                                           tobool4$2_0
                                                                                                                           (let
                                                                                                                              ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                              (let
                                                                                                                                 ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                 (let
                                                                                                                                    ((conv7$2_0 _$2_2)
                                                                                                                                     (conv8$2_0 conv$2_0))
                                                                                                                                    (let
                                                                                                                                       ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                       (=>
                                                                                                                                          cmp9$2_0
                                                                                                                                          (let
                                                                                                                                             ((retval.0$2_0 incdec.ptr$2_0))
                                                                                                                                             (let
                                                                                                                                                ((result$2 retval.0$2_0)
                                                                                                                                                 (HEAP$2_res HEAP$2))
                                                                                                                                                (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             cmp29$1_0
                                                                                             (let
                                                                                                ((retval.0$1_0 0))
                                                                                                (let
                                                                                                   ((result$1 retval.0$1_0)
                                                                                                    (HEAP$1_res HEAP$1)
                                                                                                    (conv$2_0 conv$2_0_old)
                                                                                                    (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                    (HEAP$2 HEAP$2_old)
                                                                                                    (tobool$2_0 (distinct 1 0)))
                                                                                                   (=>
                                                                                                      tobool$2_0
                                                                                                      (let
                                                                                                         ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                         (let
                                                                                                            ((conv1$2_0 _$2_0)
                                                                                                             (conv2$2_0 conv$2_0))
                                                                                                            (let
                                                                                                               ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                               (=>
                                                                                                                  (not cmp$2_0)
                                                                                                                  (let
                                                                                                                     ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                     (let
                                                                                                                        ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                        (=>
                                                                                                                           tobool4$2_0
                                                                                                                           (let
                                                                                                                              ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                              (let
                                                                                                                                 ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                 (let
                                                                                                                                    ((conv7$2_0 _$2_2)
                                                                                                                                     (conv8$2_0 conv$2_0))
                                                                                                                                    (let
                                                                                                                                       ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                       (=>
                                                                                                                                          (not cmp9$2_0)
                                                                                                                                          (let
                                                                                                                                             ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                             (let
                                                                                                                                                ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                                (=>
                                                                                                                                                   tobool13$2_0
                                                                                                                                                   (let
                                                                                                                                                      ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                                                                      (let
                                                                                                                                                         ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                         (let
                                                                                                                                                            ((conv17$2_0 _$2_4)
                                                                                                                                                             (conv18$2_0 conv$2_0))
                                                                                                                                                            (let
                                                                                                                                                               ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                                                               (=>
                                                                                                                                                                  cmp19$2_0
                                                                                                                                                                  (let
                                                                                                                                                                     ((retval.0$2_0 incdec.ptr16$2_0))
                                                                                                                                                                     (let
                                                                                                                                                                        ((result$2 retval.0$2_0)
                                                                                                                                                                         (HEAP$2_res HEAP$2))
                                                                                                                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             cmp29$1_0
                                                                                             (let
                                                                                                ((retval.0$1_0 0))
                                                                                                (let
                                                                                                   ((result$1 retval.0$1_0)
                                                                                                    (HEAP$1_res HEAP$1)
                                                                                                    (conv$2_0 conv$2_0_old)
                                                                                                    (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                    (HEAP$2 HEAP$2_old)
                                                                                                    (tobool$2_0 (distinct 1 0)))
                                                                                                   (=>
                                                                                                      tobool$2_0
                                                                                                      (let
                                                                                                         ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                         (let
                                                                                                            ((conv1$2_0 _$2_0)
                                                                                                             (conv2$2_0 conv$2_0))
                                                                                                            (let
                                                                                                               ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                               (=>
                                                                                                                  (not cmp$2_0)
                                                                                                                  (let
                                                                                                                     ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                     (let
                                                                                                                        ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                        (=>
                                                                                                                           tobool4$2_0
                                                                                                                           (let
                                                                                                                              ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                              (let
                                                                                                                                 ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                 (let
                                                                                                                                    ((conv7$2_0 _$2_2)
                                                                                                                                     (conv8$2_0 conv$2_0))
                                                                                                                                    (let
                                                                                                                                       ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                       (=>
                                                                                                                                          (not cmp9$2_0)
                                                                                                                                          (let
                                                                                                                                             ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                             (let
                                                                                                                                                ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                                (=>
                                                                                                                                                   tobool13$2_0
                                                                                                                                                   (let
                                                                                                                                                      ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                                                                      (let
                                                                                                                                                         ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                         (let
                                                                                                                                                            ((conv17$2_0 _$2_4)
                                                                                                                                                             (conv18$2_0 conv$2_0))
                                                                                                                                                            (let
                                                                                                                                                               ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                                                               (=>
                                                                                                                                                                  (not cmp19$2_0)
                                                                                                                                                                  (let
                                                                                                                                                                     ((_$2_5 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                                     (let
                                                                                                                                                                        ((tobool23$2_0 (distinct _$2_5 0)))
                                                                                                                                                                        (=>
                                                                                                                                                                           (not tobool23$2_0)
                                                                                                                                                                           (let
                                                                                                                                                                              ((retval.0$2_0 0))
                                                                                                                                                                              (let
                                                                                                                                                                                 ((result$2 retval.0$2_0)
                                                                                                                                                                                  (HEAP$2_res HEAP$2))
                                                                                                                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             cmp29$1_0
                                                                                             (let
                                                                                                ((retval.0$1_0 0))
                                                                                                (let
                                                                                                   ((result$1 retval.0$1_0)
                                                                                                    (HEAP$1_res HEAP$1)
                                                                                                    (conv$2_0 conv$2_0_old)
                                                                                                    (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                    (HEAP$2 HEAP$2_old)
                                                                                                    (tobool$2_0 (distinct 1 0)))
                                                                                                   (=>
                                                                                                      tobool$2_0
                                                                                                      (let
                                                                                                         ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                         (let
                                                                                                            ((conv1$2_0 _$2_0)
                                                                                                             (conv2$2_0 conv$2_0))
                                                                                                            (let
                                                                                                               ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                               (=>
                                                                                                                  (not cmp$2_0)
                                                                                                                  (let
                                                                                                                     ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                     (let
                                                                                                                        ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                        (=>
                                                                                                                           tobool4$2_0
                                                                                                                           (let
                                                                                                                              ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                              (let
                                                                                                                                 ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                 (let
                                                                                                                                    ((conv7$2_0 _$2_2)
                                                                                                                                     (conv8$2_0 conv$2_0))
                                                                                                                                    (let
                                                                                                                                       ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                       (=>
                                                                                                                                          (not cmp9$2_0)
                                                                                                                                          (let
                                                                                                                                             ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                             (let
                                                                                                                                                ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                                (=>
                                                                                                                                                   (not tobool13$2_0)
                                                                                                                                                   (let
                                                                                                                                                      ((retval.0$2_0 0))
                                                                                                                                                      (let
                                                                                                                                                         ((result$2 retval.0$2_0)
                                                                                                                                                          (HEAP$2_res HEAP$2))
                                                                                                                                                         (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             cmp29$1_0
                                                                                             (let
                                                                                                ((retval.0$1_0 0))
                                                                                                (let
                                                                                                   ((result$1 retval.0$1_0)
                                                                                                    (HEAP$1_res HEAP$1)
                                                                                                    (conv$2_0 conv$2_0_old)
                                                                                                    (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                    (HEAP$2 HEAP$2_old)
                                                                                                    (tobool$2_0 (distinct 1 0)))
                                                                                                   (=>
                                                                                                      tobool$2_0
                                                                                                      (let
                                                                                                         ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                         (let
                                                                                                            ((conv1$2_0 _$2_0)
                                                                                                             (conv2$2_0 conv$2_0))
                                                                                                            (let
                                                                                                               ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                               (=>
                                                                                                                  (not cmp$2_0)
                                                                                                                  (let
                                                                                                                     ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                     (let
                                                                                                                        ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                        (=>
                                                                                                                           (not tobool4$2_0)
                                                                                                                           (let
                                                                                                                              ((retval.0$2_0 0))
                                                                                                                              (let
                                                                                                                                 ((result$2 retval.0$2_0)
                                                                                                                                  (HEAP$2_res HEAP$2))
                                                                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             cmp29$1_0
                                                                                             (let
                                                                                                ((retval.0$1_0 0))
                                                                                                (let
                                                                                                   ((result$1 retval.0$1_0)
                                                                                                    (HEAP$1_res HEAP$1)
                                                                                                    (conv$2_0 conv$2_0_old)
                                                                                                    (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                    (HEAP$2 HEAP$2_old)
                                                                                                    (tobool$2_0 (distinct 1 0)))
                                                                                                   (=>
                                                                                                      (not tobool$2_0)
                                                                                                      (let
                                                                                                         ((retval.0$2_0 t.addr.0$2_0))
                                                                                                         (let
                                                                                                            ((result$2 retval.0$2_0)
                                                                                                             (HEAP$2_res HEAP$2))
                                                                                                            (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            cmp37$1_0
                                                                                                            (let
                                                                                                               ((retval.0$1_0 incdec.ptr34$1_0))
                                                                                                               (let
                                                                                                                  ((result$1 retval.0$1_0)
                                                                                                                   (HEAP$1_res HEAP$1)
                                                                                                                   (conv$2_0 conv$2_0_old)
                                                                                                                   (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                   (HEAP$2 HEAP$2_old)
                                                                                                                   (tobool$2_0 (distinct 1 0)))
                                                                                                                  (=>
                                                                                                                     tobool$2_0
                                                                                                                     (let
                                                                                                                        ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                        (let
                                                                                                                           ((conv1$2_0 _$2_0)
                                                                                                                            (conv2$2_0 conv$2_0))
                                                                                                                           (let
                                                                                                                              ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                              (=>
                                                                                                                                 cmp$2_0
                                                                                                                                 (let
                                                                                                                                    ((retval.0$2_0 t.addr.0$2_0))
                                                                                                                                    (let
                                                                                                                                       ((result$2 retval.0$2_0)
                                                                                                                                        (HEAP$2_res HEAP$2))
                                                                                                                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            cmp37$1_0
                                                                                                            (let
                                                                                                               ((retval.0$1_0 incdec.ptr34$1_0))
                                                                                                               (let
                                                                                                                  ((result$1 retval.0$1_0)
                                                                                                                   (HEAP$1_res HEAP$1)
                                                                                                                   (conv$2_0 conv$2_0_old)
                                                                                                                   (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                   (HEAP$2 HEAP$2_old)
                                                                                                                   (tobool$2_0 (distinct 1 0)))
                                                                                                                  (=>
                                                                                                                     tobool$2_0
                                                                                                                     (let
                                                                                                                        ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                        (let
                                                                                                                           ((conv1$2_0 _$2_0)
                                                                                                                            (conv2$2_0 conv$2_0))
                                                                                                                           (let
                                                                                                                              ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                              (=>
                                                                                                                                 (not cmp$2_0)
                                                                                                                                 (let
                                                                                                                                    ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                    (let
                                                                                                                                       ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                                       (=>
                                                                                                                                          tobool4$2_0
                                                                                                                                          (let
                                                                                                                                             ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                                             (let
                                                                                                                                                ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                (let
                                                                                                                                                   ((conv7$2_0 _$2_2)
                                                                                                                                                    (conv8$2_0 conv$2_0))
                                                                                                                                                   (let
                                                                                                                                                      ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                                      (=>
                                                                                                                                                         cmp9$2_0
                                                                                                                                                         (let
                                                                                                                                                            ((retval.0$2_0 incdec.ptr$2_0))
                                                                                                                                                            (let
                                                                                                                                                               ((result$2 retval.0$2_0)
                                                                                                                                                                (HEAP$2_res HEAP$2))
                                                                                                                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            cmp37$1_0
                                                                                                            (let
                                                                                                               ((retval.0$1_0 incdec.ptr34$1_0))
                                                                                                               (let
                                                                                                                  ((result$1 retval.0$1_0)
                                                                                                                   (HEAP$1_res HEAP$1)
                                                                                                                   (conv$2_0 conv$2_0_old)
                                                                                                                   (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                   (HEAP$2 HEAP$2_old)
                                                                                                                   (tobool$2_0 (distinct 1 0)))
                                                                                                                  (=>
                                                                                                                     tobool$2_0
                                                                                                                     (let
                                                                                                                        ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                        (let
                                                                                                                           ((conv1$2_0 _$2_0)
                                                                                                                            (conv2$2_0 conv$2_0))
                                                                                                                           (let
                                                                                                                              ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                              (=>
                                                                                                                                 (not cmp$2_0)
                                                                                                                                 (let
                                                                                                                                    ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                    (let
                                                                                                                                       ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                                       (=>
                                                                                                                                          tobool4$2_0
                                                                                                                                          (let
                                                                                                                                             ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                                             (let
                                                                                                                                                ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                (let
                                                                                                                                                   ((conv7$2_0 _$2_2)
                                                                                                                                                    (conv8$2_0 conv$2_0))
                                                                                                                                                   (let
                                                                                                                                                      ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                                      (=>
                                                                                                                                                         (not cmp9$2_0)
                                                                                                                                                         (let
                                                                                                                                                            ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                            (let
                                                                                                                                                               ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                                               (=>
                                                                                                                                                                  tobool13$2_0
                                                                                                                                                                  (let
                                                                                                                                                                     ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                                                                                     (let
                                                                                                                                                                        ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                                        (let
                                                                                                                                                                           ((conv17$2_0 _$2_4)
                                                                                                                                                                            (conv18$2_0 conv$2_0))
                                                                                                                                                                           (let
                                                                                                                                                                              ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                                                                              (=>
                                                                                                                                                                                 cmp19$2_0
                                                                                                                                                                                 (let
                                                                                                                                                                                    ((retval.0$2_0 incdec.ptr16$2_0))
                                                                                                                                                                                    (let
                                                                                                                                                                                       ((result$2 retval.0$2_0)
                                                                                                                                                                                        (HEAP$2_res HEAP$2))
                                                                                                                                                                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            cmp37$1_0
                                                                                                            (let
                                                                                                               ((retval.0$1_0 incdec.ptr34$1_0))
                                                                                                               (let
                                                                                                                  ((result$1 retval.0$1_0)
                                                                                                                   (HEAP$1_res HEAP$1)
                                                                                                                   (conv$2_0 conv$2_0_old)
                                                                                                                   (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                   (HEAP$2 HEAP$2_old)
                                                                                                                   (tobool$2_0 (distinct 1 0)))
                                                                                                                  (=>
                                                                                                                     tobool$2_0
                                                                                                                     (let
                                                                                                                        ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                        (let
                                                                                                                           ((conv1$2_0 _$2_0)
                                                                                                                            (conv2$2_0 conv$2_0))
                                                                                                                           (let
                                                                                                                              ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                              (=>
                                                                                                                                 (not cmp$2_0)
                                                                                                                                 (let
                                                                                                                                    ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                    (let
                                                                                                                                       ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                                       (=>
                                                                                                                                          tobool4$2_0
                                                                                                                                          (let
                                                                                                                                             ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                                             (let
                                                                                                                                                ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                (let
                                                                                                                                                   ((conv7$2_0 _$2_2)
                                                                                                                                                    (conv8$2_0 conv$2_0))
                                                                                                                                                   (let
                                                                                                                                                      ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                                      (=>
                                                                                                                                                         (not cmp9$2_0)
                                                                                                                                                         (let
                                                                                                                                                            ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                            (let
                                                                                                                                                               ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                                               (=>
                                                                                                                                                                  tobool13$2_0
                                                                                                                                                                  (let
                                                                                                                                                                     ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                                                                                     (let
                                                                                                                                                                        ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                                        (let
                                                                                                                                                                           ((conv17$2_0 _$2_4)
                                                                                                                                                                            (conv18$2_0 conv$2_0))
                                                                                                                                                                           (let
                                                                                                                                                                              ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                                                                              (=>
                                                                                                                                                                                 (not cmp19$2_0)
                                                                                                                                                                                 (let
                                                                                                                                                                                    ((_$2_5 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                                                    (let
                                                                                                                                                                                       ((tobool23$2_0 (distinct _$2_5 0)))
                                                                                                                                                                                       (=>
                                                                                                                                                                                          (not tobool23$2_0)
                                                                                                                                                                                          (let
                                                                                                                                                                                             ((retval.0$2_0 0))
                                                                                                                                                                                             (let
                                                                                                                                                                                                ((result$2 retval.0$2_0)
                                                                                                                                                                                                 (HEAP$2_res HEAP$2))
                                                                                                                                                                                                (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            cmp37$1_0
                                                                                                            (let
                                                                                                               ((retval.0$1_0 incdec.ptr34$1_0))
                                                                                                               (let
                                                                                                                  ((result$1 retval.0$1_0)
                                                                                                                   (HEAP$1_res HEAP$1)
                                                                                                                   (conv$2_0 conv$2_0_old)
                                                                                                                   (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                   (HEAP$2 HEAP$2_old)
                                                                                                                   (tobool$2_0 (distinct 1 0)))
                                                                                                                  (=>
                                                                                                                     tobool$2_0
                                                                                                                     (let
                                                                                                                        ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                        (let
                                                                                                                           ((conv1$2_0 _$2_0)
                                                                                                                            (conv2$2_0 conv$2_0))
                                                                                                                           (let
                                                                                                                              ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                              (=>
                                                                                                                                 (not cmp$2_0)
                                                                                                                                 (let
                                                                                                                                    ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                    (let
                                                                                                                                       ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                                       (=>
                                                                                                                                          tobool4$2_0
                                                                                                                                          (let
                                                                                                                                             ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                                             (let
                                                                                                                                                ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                (let
                                                                                                                                                   ((conv7$2_0 _$2_2)
                                                                                                                                                    (conv8$2_0 conv$2_0))
                                                                                                                                                   (let
                                                                                                                                                      ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                                      (=>
                                                                                                                                                         (not cmp9$2_0)
                                                                                                                                                         (let
                                                                                                                                                            ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                            (let
                                                                                                                                                               ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                                               (=>
                                                                                                                                                                  (not tobool13$2_0)
                                                                                                                                                                  (let
                                                                                                                                                                     ((retval.0$2_0 0))
                                                                                                                                                                     (let
                                                                                                                                                                        ((result$2 retval.0$2_0)
                                                                                                                                                                         (HEAP$2_res HEAP$2))
                                                                                                                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            cmp37$1_0
                                                                                                            (let
                                                                                                               ((retval.0$1_0 incdec.ptr34$1_0))
                                                                                                               (let
                                                                                                                  ((result$1 retval.0$1_0)
                                                                                                                   (HEAP$1_res HEAP$1)
                                                                                                                   (conv$2_0 conv$2_0_old)
                                                                                                                   (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                   (HEAP$2 HEAP$2_old)
                                                                                                                   (tobool$2_0 (distinct 1 0)))
                                                                                                                  (=>
                                                                                                                     tobool$2_0
                                                                                                                     (let
                                                                                                                        ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                        (let
                                                                                                                           ((conv1$2_0 _$2_0)
                                                                                                                            (conv2$2_0 conv$2_0))
                                                                                                                           (let
                                                                                                                              ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                              (=>
                                                                                                                                 (not cmp$2_0)
                                                                                                                                 (let
                                                                                                                                    ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                    (let
                                                                                                                                       ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                                       (=>
                                                                                                                                          (not tobool4$2_0)
                                                                                                                                          (let
                                                                                                                                             ((retval.0$2_0 0))
                                                                                                                                             (let
                                                                                                                                                ((result$2 retval.0$2_0)
                                                                                                                                                 (HEAP$2_res HEAP$2))
                                                                                                                                                (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            cmp37$1_0
                                                                                                            (let
                                                                                                               ((retval.0$1_0 incdec.ptr34$1_0))
                                                                                                               (let
                                                                                                                  ((result$1 retval.0$1_0)
                                                                                                                   (HEAP$1_res HEAP$1)
                                                                                                                   (conv$2_0 conv$2_0_old)
                                                                                                                   (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                   (HEAP$2 HEAP$2_old)
                                                                                                                   (tobool$2_0 (distinct 1 0)))
                                                                                                                  (=>
                                                                                                                     (not tobool$2_0)
                                                                                                                     (let
                                                                                                                        ((retval.0$2_0 t.addr.0$2_0))
                                                                                                                        (let
                                                                                                                           ((result$2 retval.0$2_0)
                                                                                                                            (HEAP$2_res HEAP$2))
                                                                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            (not cmp37$1_0)
                                                                                                            (let
                                                                                                               ((_$1_7 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                               (let
                                                                                                                  ((conv41$1_0 _$1_7))
                                                                                                                  (let
                                                                                                                     ((cmp42$1_0 (= conv41$1_0 0)))
                                                                                                                     (=>
                                                                                                                        cmp42$1_0
                                                                                                                        (let
                                                                                                                           ((retval.0$1_0 0))
                                                                                                                           (let
                                                                                                                              ((result$1 retval.0$1_0)
                                                                                                                               (HEAP$1_res HEAP$1)
                                                                                                                               (conv$2_0 conv$2_0_old)
                                                                                                                               (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                               (HEAP$2 HEAP$2_old)
                                                                                                                               (tobool$2_0 (distinct 1 0)))
                                                                                                                              (=>
                                                                                                                                 tobool$2_0
                                                                                                                                 (let
                                                                                                                                    ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                    (let
                                                                                                                                       ((conv1$2_0 _$2_0)
                                                                                                                                        (conv2$2_0 conv$2_0))
                                                                                                                                       (let
                                                                                                                                          ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                                          (=>
                                                                                                                                             cmp$2_0
                                                                                                                                             (let
                                                                                                                                                ((retval.0$2_0 t.addr.0$2_0))
                                                                                                                                                (let
                                                                                                                                                   ((result$2 retval.0$2_0)
                                                                                                                                                    (HEAP$2_res HEAP$2))
                                                                                                                                                   (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            (not cmp37$1_0)
                                                                                                            (let
                                                                                                               ((_$1_7 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                               (let
                                                                                                                  ((conv41$1_0 _$1_7))
                                                                                                                  (let
                                                                                                                     ((cmp42$1_0 (= conv41$1_0 0)))
                                                                                                                     (=>
                                                                                                                        cmp42$1_0
                                                                                                                        (let
                                                                                                                           ((retval.0$1_0 0))
                                                                                                                           (let
                                                                                                                              ((result$1 retval.0$1_0)
                                                                                                                               (HEAP$1_res HEAP$1)
                                                                                                                               (conv$2_0 conv$2_0_old)
                                                                                                                               (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                               (HEAP$2 HEAP$2_old)
                                                                                                                               (tobool$2_0 (distinct 1 0)))
                                                                                                                              (=>
                                                                                                                                 tobool$2_0
                                                                                                                                 (let
                                                                                                                                    ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                    (let
                                                                                                                                       ((conv1$2_0 _$2_0)
                                                                                                                                        (conv2$2_0 conv$2_0))
                                                                                                                                       (let
                                                                                                                                          ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                                          (=>
                                                                                                                                             (not cmp$2_0)
                                                                                                                                             (let
                                                                                                                                                ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                                (let
                                                                                                                                                   ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                                                   (=>
                                                                                                                                                      tobool4$2_0
                                                                                                                                                      (let
                                                                                                                                                         ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                                                         (let
                                                                                                                                                            ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                            (let
                                                                                                                                                               ((conv7$2_0 _$2_2)
                                                                                                                                                                (conv8$2_0 conv$2_0))
                                                                                                                                                               (let
                                                                                                                                                                  ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                                                  (=>
                                                                                                                                                                     cmp9$2_0
                                                                                                                                                                     (let
                                                                                                                                                                        ((retval.0$2_0 incdec.ptr$2_0))
                                                                                                                                                                        (let
                                                                                                                                                                           ((result$2 retval.0$2_0)
                                                                                                                                                                            (HEAP$2_res HEAP$2))
                                                                                                                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            (not cmp37$1_0)
                                                                                                            (let
                                                                                                               ((_$1_7 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                               (let
                                                                                                                  ((conv41$1_0 _$1_7))
                                                                                                                  (let
                                                                                                                     ((cmp42$1_0 (= conv41$1_0 0)))
                                                                                                                     (=>
                                                                                                                        cmp42$1_0
                                                                                                                        (let
                                                                                                                           ((retval.0$1_0 0))
                                                                                                                           (let
                                                                                                                              ((result$1 retval.0$1_0)
                                                                                                                               (HEAP$1_res HEAP$1)
                                                                                                                               (conv$2_0 conv$2_0_old)
                                                                                                                               (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                               (HEAP$2 HEAP$2_old)
                                                                                                                               (tobool$2_0 (distinct 1 0)))
                                                                                                                              (=>
                                                                                                                                 tobool$2_0
                                                                                                                                 (let
                                                                                                                                    ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                    (let
                                                                                                                                       ((conv1$2_0 _$2_0)
                                                                                                                                        (conv2$2_0 conv$2_0))
                                                                                                                                       (let
                                                                                                                                          ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                                          (=>
                                                                                                                                             (not cmp$2_0)
                                                                                                                                             (let
                                                                                                                                                ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                                (let
                                                                                                                                                   ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                                                   (=>
                                                                                                                                                      tobool4$2_0
                                                                                                                                                      (let
                                                                                                                                                         ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                                                         (let
                                                                                                                                                            ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                            (let
                                                                                                                                                               ((conv7$2_0 _$2_2)
                                                                                                                                                                (conv8$2_0 conv$2_0))
                                                                                                                                                               (let
                                                                                                                                                                  ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                                                  (=>
                                                                                                                                                                     (not cmp9$2_0)
                                                                                                                                                                     (let
                                                                                                                                                                        ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                                        (let
                                                                                                                                                                           ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                                                           (=>
                                                                                                                                                                              tobool13$2_0
                                                                                                                                                                              (let
                                                                                                                                                                                 ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                                                                                                 (let
                                                                                                                                                                                    ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                                                    (let
                                                                                                                                                                                       ((conv17$2_0 _$2_4)
                                                                                                                                                                                        (conv18$2_0 conv$2_0))
                                                                                                                                                                                       (let
                                                                                                                                                                                          ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                                                                                          (=>
                                                                                                                                                                                             cmp19$2_0
                                                                                                                                                                                             (let
                                                                                                                                                                                                ((retval.0$2_0 incdec.ptr16$2_0))
                                                                                                                                                                                                (let
                                                                                                                                                                                                   ((result$2 retval.0$2_0)
                                                                                                                                                                                                    (HEAP$2_res HEAP$2))
                                                                                                                                                                                                   (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            (not cmp37$1_0)
                                                                                                            (let
                                                                                                               ((_$1_7 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                               (let
                                                                                                                  ((conv41$1_0 _$1_7))
                                                                                                                  (let
                                                                                                                     ((cmp42$1_0 (= conv41$1_0 0)))
                                                                                                                     (=>
                                                                                                                        cmp42$1_0
                                                                                                                        (let
                                                                                                                           ((retval.0$1_0 0))
                                                                                                                           (let
                                                                                                                              ((result$1 retval.0$1_0)
                                                                                                                               (HEAP$1_res HEAP$1)
                                                                                                                               (conv$2_0 conv$2_0_old)
                                                                                                                               (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                               (HEAP$2 HEAP$2_old)
                                                                                                                               (tobool$2_0 (distinct 1 0)))
                                                                                                                              (=>
                                                                                                                                 tobool$2_0
                                                                                                                                 (let
                                                                                                                                    ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                    (let
                                                                                                                                       ((conv1$2_0 _$2_0)
                                                                                                                                        (conv2$2_0 conv$2_0))
                                                                                                                                       (let
                                                                                                                                          ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                                          (=>
                                                                                                                                             (not cmp$2_0)
                                                                                                                                             (let
                                                                                                                                                ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                                (let
                                                                                                                                                   ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                                                   (=>
                                                                                                                                                      tobool4$2_0
                                                                                                                                                      (let
                                                                                                                                                         ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                                                         (let
                                                                                                                                                            ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                            (let
                                                                                                                                                               ((conv7$2_0 _$2_2)
                                                                                                                                                                (conv8$2_0 conv$2_0))
                                                                                                                                                               (let
                                                                                                                                                                  ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                                                  (=>
                                                                                                                                                                     (not cmp9$2_0)
                                                                                                                                                                     (let
                                                                                                                                                                        ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                                        (let
                                                                                                                                                                           ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                                                           (=>
                                                                                                                                                                              tobool13$2_0
                                                                                                                                                                              (let
                                                                                                                                                                                 ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                                                                                                 (let
                                                                                                                                                                                    ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                                                    (let
                                                                                                                                                                                       ((conv17$2_0 _$2_4)
                                                                                                                                                                                        (conv18$2_0 conv$2_0))
                                                                                                                                                                                       (let
                                                                                                                                                                                          ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                                                                                          (=>
                                                                                                                                                                                             (not cmp19$2_0)
                                                                                                                                                                                             (let
                                                                                                                                                                                                ((_$2_5 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                                                                (let
                                                                                                                                                                                                   ((tobool23$2_0 (distinct _$2_5 0)))
                                                                                                                                                                                                   (=>
                                                                                                                                                                                                      (not tobool23$2_0)
                                                                                                                                                                                                      (let
                                                                                                                                                                                                         ((retval.0$2_0 0))
                                                                                                                                                                                                         (let
                                                                                                                                                                                                            ((result$2 retval.0$2_0)
                                                                                                                                                                                                             (HEAP$2_res HEAP$2))
                                                                                                                                                                                                            (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            (not cmp37$1_0)
                                                                                                            (let
                                                                                                               ((_$1_7 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                               (let
                                                                                                                  ((conv41$1_0 _$1_7))
                                                                                                                  (let
                                                                                                                     ((cmp42$1_0 (= conv41$1_0 0)))
                                                                                                                     (=>
                                                                                                                        cmp42$1_0
                                                                                                                        (let
                                                                                                                           ((retval.0$1_0 0))
                                                                                                                           (let
                                                                                                                              ((result$1 retval.0$1_0)
                                                                                                                               (HEAP$1_res HEAP$1)
                                                                                                                               (conv$2_0 conv$2_0_old)
                                                                                                                               (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                               (HEAP$2 HEAP$2_old)
                                                                                                                               (tobool$2_0 (distinct 1 0)))
                                                                                                                              (=>
                                                                                                                                 tobool$2_0
                                                                                                                                 (let
                                                                                                                                    ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                    (let
                                                                                                                                       ((conv1$2_0 _$2_0)
                                                                                                                                        (conv2$2_0 conv$2_0))
                                                                                                                                       (let
                                                                                                                                          ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                                          (=>
                                                                                                                                             (not cmp$2_0)
                                                                                                                                             (let
                                                                                                                                                ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                                (let
                                                                                                                                                   ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                                                   (=>
                                                                                                                                                      tobool4$2_0
                                                                                                                                                      (let
                                                                                                                                                         ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                                                         (let
                                                                                                                                                            ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                            (let
                                                                                                                                                               ((conv7$2_0 _$2_2)
                                                                                                                                                                (conv8$2_0 conv$2_0))
                                                                                                                                                               (let
                                                                                                                                                                  ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                                                  (=>
                                                                                                                                                                     (not cmp9$2_0)
                                                                                                                                                                     (let
                                                                                                                                                                        ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                                        (let
                                                                                                                                                                           ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                                                           (=>
                                                                                                                                                                              (not tobool13$2_0)
                                                                                                                                                                              (let
                                                                                                                                                                                 ((retval.0$2_0 0))
                                                                                                                                                                                 (let
                                                                                                                                                                                    ((result$2 retval.0$2_0)
                                                                                                                                                                                     (HEAP$2_res HEAP$2))
                                                                                                                                                                                    (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            (not cmp37$1_0)
                                                                                                            (let
                                                                                                               ((_$1_7 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                               (let
                                                                                                                  ((conv41$1_0 _$1_7))
                                                                                                                  (let
                                                                                                                     ((cmp42$1_0 (= conv41$1_0 0)))
                                                                                                                     (=>
                                                                                                                        cmp42$1_0
                                                                                                                        (let
                                                                                                                           ((retval.0$1_0 0))
                                                                                                                           (let
                                                                                                                              ((result$1 retval.0$1_0)
                                                                                                                               (HEAP$1_res HEAP$1)
                                                                                                                               (conv$2_0 conv$2_0_old)
                                                                                                                               (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                               (HEAP$2 HEAP$2_old)
                                                                                                                               (tobool$2_0 (distinct 1 0)))
                                                                                                                              (=>
                                                                                                                                 tobool$2_0
                                                                                                                                 (let
                                                                                                                                    ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                    (let
                                                                                                                                       ((conv1$2_0 _$2_0)
                                                                                                                                        (conv2$2_0 conv$2_0))
                                                                                                                                       (let
                                                                                                                                          ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                                          (=>
                                                                                                                                             (not cmp$2_0)
                                                                                                                                             (let
                                                                                                                                                ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                                (let
                                                                                                                                                   ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                                                   (=>
                                                                                                                                                      (not tobool4$2_0)
                                                                                                                                                      (let
                                                                                                                                                         ((retval.0$2_0 0))
                                                                                                                                                         (let
                                                                                                                                                            ((result$2 retval.0$2_0)
                                                                                                                                                             (HEAP$2_res HEAP$2))
                                                                                                                                                            (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            (not cmp37$1_0)
                                                                                                            (let
                                                                                                               ((_$1_7 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                               (let
                                                                                                                  ((conv41$1_0 _$1_7))
                                                                                                                  (let
                                                                                                                     ((cmp42$1_0 (= conv41$1_0 0)))
                                                                                                                     (=>
                                                                                                                        cmp42$1_0
                                                                                                                        (let
                                                                                                                           ((retval.0$1_0 0))
                                                                                                                           (let
                                                                                                                              ((result$1 retval.0$1_0)
                                                                                                                               (HEAP$1_res HEAP$1)
                                                                                                                               (conv$2_0 conv$2_0_old)
                                                                                                                               (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                               (HEAP$2 HEAP$2_old)
                                                                                                                               (tobool$2_0 (distinct 1 0)))
                                                                                                                              (=>
                                                                                                                                 (not tobool$2_0)
                                                                                                                                 (let
                                                                                                                                    ((retval.0$2_0 t.addr.0$2_0))
                                                                                                                                    (let
                                                                                                                                       ((result$2 retval.0$2_0)
                                                                                                                                        (HEAP$2_res HEAP$2))
                                                                                                                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               (not tobool$1_0)
               (let
                  ((retval.0$1_0 0))
                  (let
                     ((result$1 retval.0$1_0)
                      (HEAP$1_res HEAP$1)
                      (conv$2_0 conv$2_0_old)
                      (t.addr.0$2_0 t.addr.0$2_0_old)
                      (HEAP$2 HEAP$2_old)
                      (tobool$2_0 (distinct 1 0)))
                     (=>
                        tobool$2_0
                        (let
                           ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                           (let
                              ((conv1$2_0 _$2_0)
                               (conv2$2_0 conv$2_0))
                              (let
                                 ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                 (=>
                                    cmp$2_0
                                    (let
                                       ((retval.0$2_0 t.addr.0$2_0))
                                       (let
                                          ((result$2 retval.0$2_0)
                                           (HEAP$2_res HEAP$2))
                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               (not tobool$1_0)
               (let
                  ((retval.0$1_0 0))
                  (let
                     ((result$1 retval.0$1_0)
                      (HEAP$1_res HEAP$1)
                      (conv$2_0 conv$2_0_old)
                      (t.addr.0$2_0 t.addr.0$2_0_old)
                      (HEAP$2 HEAP$2_old)
                      (tobool$2_0 (distinct 1 0)))
                     (=>
                        tobool$2_0
                        (let
                           ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                           (let
                              ((conv1$2_0 _$2_0)
                               (conv2$2_0 conv$2_0))
                              (let
                                 ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                 (=>
                                    (not cmp$2_0)
                                    (let
                                       ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                       (let
                                          ((tobool4$2_0 (distinct _$2_1 0)))
                                          (=>
                                             tobool4$2_0
                                             (let
                                                ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                (let
                                                   ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                   (let
                                                      ((conv7$2_0 _$2_2)
                                                       (conv8$2_0 conv$2_0))
                                                      (let
                                                         ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                         (=>
                                                            cmp9$2_0
                                                            (let
                                                               ((retval.0$2_0 incdec.ptr$2_0))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               (not tobool$1_0)
               (let
                  ((retval.0$1_0 0))
                  (let
                     ((result$1 retval.0$1_0)
                      (HEAP$1_res HEAP$1)
                      (conv$2_0 conv$2_0_old)
                      (t.addr.0$2_0 t.addr.0$2_0_old)
                      (HEAP$2 HEAP$2_old)
                      (tobool$2_0 (distinct 1 0)))
                     (=>
                        tobool$2_0
                        (let
                           ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                           (let
                              ((conv1$2_0 _$2_0)
                               (conv2$2_0 conv$2_0))
                              (let
                                 ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                 (=>
                                    (not cmp$2_0)
                                    (let
                                       ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                       (let
                                          ((tobool4$2_0 (distinct _$2_1 0)))
                                          (=>
                                             tobool4$2_0
                                             (let
                                                ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                (let
                                                   ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                   (let
                                                      ((conv7$2_0 _$2_2)
                                                       (conv8$2_0 conv$2_0))
                                                      (let
                                                         ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                         (=>
                                                            (not cmp9$2_0)
                                                            (let
                                                               ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                               (let
                                                                  ((tobool13$2_0 (distinct _$2_3 0)))
                                                                  (=>
                                                                     tobool13$2_0
                                                                     (let
                                                                        ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                        (let
                                                                           ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                           (let
                                                                              ((conv17$2_0 _$2_4)
                                                                               (conv18$2_0 conv$2_0))
                                                                              (let
                                                                                 ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                 (=>
                                                                                    cmp19$2_0
                                                                                    (let
                                                                                       ((retval.0$2_0 incdec.ptr16$2_0))
                                                                                       (let
                                                                                          ((result$2 retval.0$2_0)
                                                                                           (HEAP$2_res HEAP$2))
                                                                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               (not tobool$1_0)
               (let
                  ((retval.0$1_0 0))
                  (let
                     ((result$1 retval.0$1_0)
                      (HEAP$1_res HEAP$1)
                      (conv$2_0 conv$2_0_old)
                      (t.addr.0$2_0 t.addr.0$2_0_old)
                      (HEAP$2 HEAP$2_old)
                      (tobool$2_0 (distinct 1 0)))
                     (=>
                        tobool$2_0
                        (let
                           ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                           (let
                              ((conv1$2_0 _$2_0)
                               (conv2$2_0 conv$2_0))
                              (let
                                 ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                 (=>
                                    (not cmp$2_0)
                                    (let
                                       ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                       (let
                                          ((tobool4$2_0 (distinct _$2_1 0)))
                                          (=>
                                             tobool4$2_0
                                             (let
                                                ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                (let
                                                   ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                   (let
                                                      ((conv7$2_0 _$2_2)
                                                       (conv8$2_0 conv$2_0))
                                                      (let
                                                         ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                         (=>
                                                            (not cmp9$2_0)
                                                            (let
                                                               ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                               (let
                                                                  ((tobool13$2_0 (distinct _$2_3 0)))
                                                                  (=>
                                                                     tobool13$2_0
                                                                     (let
                                                                        ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                        (let
                                                                           ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                           (let
                                                                              ((conv17$2_0 _$2_4)
                                                                               (conv18$2_0 conv$2_0))
                                                                              (let
                                                                                 ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                 (=>
                                                                                    (not cmp19$2_0)
                                                                                    (let
                                                                                       ((_$2_5 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                       (let
                                                                                          ((tobool23$2_0 (distinct _$2_5 0)))
                                                                                          (=>
                                                                                             (not tobool23$2_0)
                                                                                             (let
                                                                                                ((retval.0$2_0 0))
                                                                                                (let
                                                                                                   ((result$2 retval.0$2_0)
                                                                                                    (HEAP$2_res HEAP$2))
                                                                                                   (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               (not tobool$1_0)
               (let
                  ((retval.0$1_0 0))
                  (let
                     ((result$1 retval.0$1_0)
                      (HEAP$1_res HEAP$1)
                      (conv$2_0 conv$2_0_old)
                      (t.addr.0$2_0 t.addr.0$2_0_old)
                      (HEAP$2 HEAP$2_old)
                      (tobool$2_0 (distinct 1 0)))
                     (=>
                        tobool$2_0
                        (let
                           ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                           (let
                              ((conv1$2_0 _$2_0)
                               (conv2$2_0 conv$2_0))
                              (let
                                 ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                 (=>
                                    (not cmp$2_0)
                                    (let
                                       ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                       (let
                                          ((tobool4$2_0 (distinct _$2_1 0)))
                                          (=>
                                             tobool4$2_0
                                             (let
                                                ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                (let
                                                   ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                   (let
                                                      ((conv7$2_0 _$2_2)
                                                       (conv8$2_0 conv$2_0))
                                                      (let
                                                         ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                         (=>
                                                            (not cmp9$2_0)
                                                            (let
                                                               ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                               (let
                                                                  ((tobool13$2_0 (distinct _$2_3 0)))
                                                                  (=>
                                                                     (not tobool13$2_0)
                                                                     (let
                                                                        ((retval.0$2_0 0))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               (not tobool$1_0)
               (let
                  ((retval.0$1_0 0))
                  (let
                     ((result$1 retval.0$1_0)
                      (HEAP$1_res HEAP$1)
                      (conv$2_0 conv$2_0_old)
                      (t.addr.0$2_0 t.addr.0$2_0_old)
                      (HEAP$2 HEAP$2_old)
                      (tobool$2_0 (distinct 1 0)))
                     (=>
                        tobool$2_0
                        (let
                           ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                           (let
                              ((conv1$2_0 _$2_0)
                               (conv2$2_0 conv$2_0))
                              (let
                                 ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                 (=>
                                    (not cmp$2_0)
                                    (let
                                       ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                       (let
                                          ((tobool4$2_0 (distinct _$2_1 0)))
                                          (=>
                                             (not tobool4$2_0)
                                             (let
                                                ((retval.0$2_0 0))
                                                (let
                                                   ((result$2 retval.0$2_0)
                                                    (HEAP$2_res HEAP$2))
                                                   (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               (not tobool$1_0)
               (let
                  ((retval.0$1_0 0))
                  (let
                     ((result$1 retval.0$1_0)
                      (HEAP$1_res HEAP$1)
                      (conv$2_0 conv$2_0_old)
                      (t.addr.0$2_0 t.addr.0$2_0_old)
                      (HEAP$2 HEAP$2_old)
                      (tobool$2_0 (distinct 1 0)))
                     (=>
                        (not tobool$2_0)
                        (let
                           ((retval.0$2_0 t.addr.0$2_0))
                           (let
                              ((result$2 retval.0$2_0)
                               (HEAP$2_res HEAP$2))
                              (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            (not cmp37$1_0)
                                                                                                            (let
                                                                                                               ((_$1_7 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                               (let
                                                                                                                  ((conv41$1_0 _$1_7))
                                                                                                                  (let
                                                                                                                     ((cmp42$1_0 (= conv41$1_0 0)))
                                                                                                                     (=>
                                                                                                                        (not cmp42$1_0)
                                                                                                                        (let
                                                                                                                           ((s.addr.0$1_0 incdec.ptr34$1_0)
                                                                                                                            (conv$2_0 conv$2_0_old)
                                                                                                                            (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                            (HEAP$2 HEAP$2_old)
                                                                                                                            (tobool$2_0 (distinct 1 0)))
                                                                                                                           (=>
                                                                                                                              tobool$2_0
                                                                                                                              (let
                                                                                                                                 ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                 (let
                                                                                                                                    ((conv1$2_0 _$2_0)
                                                                                                                                     (conv2$2_0 conv$2_0))
                                                                                                                                    (let
                                                                                                                                       ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                                       (=>
                                                                                                                                          (not cmp$2_0)
                                                                                                                                          (let
                                                                                                                                             ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                             (let
                                                                                                                                                ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                                                (=>
                                                                                                                                                   tobool4$2_0
                                                                                                                                                   (let
                                                                                                                                                      ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                                                      (let
                                                                                                                                                         ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                         (let
                                                                                                                                                            ((conv7$2_0 _$2_2)
                                                                                                                                                             (conv8$2_0 conv$2_0))
                                                                                                                                                            (let
                                                                                                                                                               ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                                               (=>
                                                                                                                                                                  (not cmp9$2_0)
                                                                                                                                                                  (let
                                                                                                                                                                     ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                                     (let
                                                                                                                                                                        ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                                                        (=>
                                                                                                                                                                           tobool13$2_0
                                                                                                                                                                           (let
                                                                                                                                                                              ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                                                                                              (let
                                                                                                                                                                                 ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                                                 (let
                                                                                                                                                                                    ((conv17$2_0 _$2_4)
                                                                                                                                                                                     (conv18$2_0 conv$2_0))
                                                                                                                                                                                    (let
                                                                                                                                                                                       ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                                                                                       (=>
                                                                                                                                                                                          (not cmp19$2_0)
                                                                                                                                                                                          (let
                                                                                                                                                                                             ((_$2_5 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                                                             (let
                                                                                                                                                                                                ((tobool23$2_0 (distinct _$2_5 0)))
                                                                                                                                                                                                (=>
                                                                                                                                                                                                   tobool23$2_0
                                                                                                                                                                                                   (let
                                                                                                                                                                                                      ((incdec.ptr26$2_0 (+ incdec.ptr16$2_0 1)))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                         ((t.addr.0$2_0 incdec.ptr26$2_0))
                                                                                                                                                                                                         (forall
                                                                                                                                                                                                            ((i1 Int)
                                                                                                                                                                                                             (i2 Int))
                                                                                                                                                                                                            (INV_MAIN_42 conv$1_0 s.addr.0$1_0 i1 (select HEAP$1 i1) conv$2_0 t.addr.0$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$1_0 conv$1_0_old)
             (s.addr.0$1_0 s.addr.0$1_0_old)
             (HEAP$1 HEAP$1_old)
             (tobool$1_0 (distinct 1 0)))
            (=>
               tobool$1_0
               (let
                  ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                  (let
                     ((conv1$1_0 _$1_0)
                      (conv2$1_0 conv$1_0))
                     (let
                        ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                        (=>
                           (not cmp$1_0)
                           (let
                              ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                              (let
                                 ((conv4$1_0 _$1_1))
                                 (let
                                    ((cmp5$1_0 (= conv4$1_0 0)))
                                    (=>
                                       (not cmp5$1_0)
                                       (let
                                          ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                          (let
                                             ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                             (let
                                                ((conv9$1_0 _$1_2)
                                                 (conv10$1_0 conv$1_0))
                                                (let
                                                   ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                   (=>
                                                      (not cmp11$1_0)
                                                      (let
                                                         ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                         (let
                                                            ((conv15$1_0 _$1_3))
                                                            (let
                                                               ((cmp16$1_0 (= conv15$1_0 0)))
                                                               (=>
                                                                  (not cmp16$1_0)
                                                                  (let
                                                                     ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                     (let
                                                                        ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                        (let
                                                                           ((conv22$1_0 _$1_4)
                                                                            (conv23$1_0 conv$1_0))
                                                                           (let
                                                                              ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                              (=>
                                                                                 (not cmp24$1_0)
                                                                                 (let
                                                                                    ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                    (let
                                                                                       ((conv28$1_0 _$1_5))
                                                                                       (let
                                                                                          ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                          (=>
                                                                                             (not cmp29$1_0)
                                                                                             (let
                                                                                                ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                (let
                                                                                                   ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                   (let
                                                                                                      ((conv35$1_0 _$1_6)
                                                                                                       (conv36$1_0 conv$1_0))
                                                                                                      (let
                                                                                                         ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                         (=>
                                                                                                            (not cmp37$1_0)
                                                                                                            (let
                                                                                                               ((_$1_7 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                               (let
                                                                                                                  ((conv41$1_0 _$1_7))
                                                                                                                  (let
                                                                                                                     ((cmp42$1_0 (= conv41$1_0 0)))
                                                                                                                     (=>
                                                                                                                        (not cmp42$1_0)
                                                                                                                        (let
                                                                                                                           ((s.addr.0$1_0 incdec.ptr34$1_0))
                                                                                                                           (=>
                                                                                                                              (let
                                                                                                                                 ((conv$2_0 conv$2_0_old)
                                                                                                                                  (t.addr.0$2_0 t.addr.0$2_0_old)
                                                                                                                                  (HEAP$2 HEAP$2_old)
                                                                                                                                  (tobool$2_0 (distinct 1 0)))
                                                                                                                                 (=>
                                                                                                                                    tobool$2_0
                                                                                                                                    (let
                                                                                                                                       ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                       (let
                                                                                                                                          ((conv1$2_0 _$2_0)
                                                                                                                                           (conv2$2_0 conv$2_0))
                                                                                                                                          (let
                                                                                                                                             ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                                                                                                                                             (=>
                                                                                                                                                (not cmp$2_0)
                                                                                                                                                (let
                                                                                                                                                   ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                                                                                                                                                   (let
                                                                                                                                                      ((tobool4$2_0 (distinct _$2_1 0)))
                                                                                                                                                      (=>
                                                                                                                                                         tobool4$2_0
                                                                                                                                                         (let
                                                                                                                                                            ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                                                                                                                                            (let
                                                                                                                                                               ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                               (let
                                                                                                                                                                  ((conv7$2_0 _$2_2)
                                                                                                                                                                   (conv8$2_0 conv$2_0))
                                                                                                                                                                  (let
                                                                                                                                                                     ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                                                                                                                                     (=>
                                                                                                                                                                        (not cmp9$2_0)
                                                                                                                                                                        (let
                                                                                                                                                                           ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                                                                                                                                           (let
                                                                                                                                                                              ((tobool13$2_0 (distinct _$2_3 0)))
                                                                                                                                                                              (=>
                                                                                                                                                                                 tobool13$2_0
                                                                                                                                                                                 (let
                                                                                                                                                                                    ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                                                                                                                                                    (let
                                                                                                                                                                                       ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                                                       (let
                                                                                                                                                                                          ((conv17$2_0 _$2_4)
                                                                                                                                                                                           (conv18$2_0 conv$2_0))
                                                                                                                                                                                          (let
                                                                                                                                                                                             ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                                                                                                                                             (=>
                                                                                                                                                                                                (not cmp19$2_0)
                                                                                                                                                                                                (let
                                                                                                                                                                                                   ((_$2_5 (select HEAP$2 incdec.ptr16$2_0)))
                                                                                                                                                                                                   (let
                                                                                                                                                                                                      ((tobool23$2_0 (distinct _$2_5 0)))
                                                                                                                                                                                                      (=>
                                                                                                                                                                                                         tobool23$2_0
                                                                                                                                                                                                         (let
                                                                                                                                                                                                            ((incdec.ptr26$2_0 (+ incdec.ptr16$2_0 1)))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                               ((t.addr.0$2_0 incdec.ptr26$2_0))
                                                                                                                                                                                                               false)))))))))))))))))))))))))))
                                                                                                                              (forall
                                                                                                                                 ((i1 Int)
                                                                                                                                  (i2_old Int))
                                                                                                                                 (INV_MAIN_42 conv$1_0 s.addr.0$1_0 i1 (select HEAP$1 i1) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((conv$1_0_old Int)
       (s.addr.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (conv$2_0_old Int)
       (t.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0_old t.addr.0$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((conv$2_0 conv$2_0_old)
             (t.addr.0$2_0 t.addr.0$2_0_old)
             (HEAP$2 HEAP$2_old)
             (tobool$2_0 (distinct 1 0)))
            (=>
               tobool$2_0
               (let
                  ((_$2_0 (select HEAP$2 t.addr.0$2_0)))
                  (let
                     ((conv1$2_0 _$2_0)
                      (conv2$2_0 conv$2_0))
                     (let
                        ((cmp$2_0 (= conv1$2_0 conv2$2_0)))
                        (=>
                           (not cmp$2_0)
                           (let
                              ((_$2_1 (select HEAP$2 t.addr.0$2_0)))
                              (let
                                 ((tobool4$2_0 (distinct _$2_1 0)))
                                 (=>
                                    tobool4$2_0
                                    (let
                                       ((incdec.ptr$2_0 (+ t.addr.0$2_0 1)))
                                       (let
                                          ((_$2_2 (select HEAP$2 incdec.ptr$2_0)))
                                          (let
                                             ((conv7$2_0 _$2_2)
                                              (conv8$2_0 conv$2_0))
                                             (let
                                                ((cmp9$2_0 (= conv7$2_0 conv8$2_0)))
                                                (=>
                                                   (not cmp9$2_0)
                                                   (let
                                                      ((_$2_3 (select HEAP$2 incdec.ptr$2_0)))
                                                      (let
                                                         ((tobool13$2_0 (distinct _$2_3 0)))
                                                         (=>
                                                            tobool13$2_0
                                                            (let
                                                               ((incdec.ptr16$2_0 (+ incdec.ptr$2_0 1)))
                                                               (let
                                                                  ((_$2_4 (select HEAP$2 incdec.ptr16$2_0)))
                                                                  (let
                                                                     ((conv17$2_0 _$2_4)
                                                                      (conv18$2_0 conv$2_0))
                                                                     (let
                                                                        ((cmp19$2_0 (= conv17$2_0 conv18$2_0)))
                                                                        (=>
                                                                           (not cmp19$2_0)
                                                                           (let
                                                                              ((_$2_5 (select HEAP$2 incdec.ptr16$2_0)))
                                                                              (let
                                                                                 ((tobool23$2_0 (distinct _$2_5 0)))
                                                                                 (=>
                                                                                    tobool23$2_0
                                                                                    (let
                                                                                       ((incdec.ptr26$2_0 (+ incdec.ptr16$2_0 1)))
                                                                                       (let
                                                                                          ((t.addr.0$2_0 incdec.ptr26$2_0))
                                                                                          (=>
                                                                                             (let
                                                                                                ((conv$1_0 conv$1_0_old)
                                                                                                 (s.addr.0$1_0 s.addr.0$1_0_old)
                                                                                                 (HEAP$1 HEAP$1_old)
                                                                                                 (tobool$1_0 (distinct 1 0)))
                                                                                                (=>
                                                                                                   tobool$1_0
                                                                                                   (let
                                                                                                      ((_$1_0 (select HEAP$1 s.addr.0$1_0)))
                                                                                                      (let
                                                                                                         ((conv1$1_0 _$1_0)
                                                                                                          (conv2$1_0 conv$1_0))
                                                                                                         (let
                                                                                                            ((cmp$1_0 (= conv1$1_0 conv2$1_0)))
                                                                                                            (=>
                                                                                                               (not cmp$1_0)
                                                                                                               (let
                                                                                                                  ((_$1_1 (select HEAP$1 s.addr.0$1_0)))
                                                                                                                  (let
                                                                                                                     ((conv4$1_0 _$1_1))
                                                                                                                     (let
                                                                                                                        ((cmp5$1_0 (= conv4$1_0 0)))
                                                                                                                        (=>
                                                                                                                           (not cmp5$1_0)
                                                                                                                           (let
                                                                                                                              ((incdec.ptr$1_0 (+ s.addr.0$1_0 1)))
                                                                                                                              (let
                                                                                                                                 ((_$1_2 (select HEAP$1 incdec.ptr$1_0)))
                                                                                                                                 (let
                                                                                                                                    ((conv9$1_0 _$1_2)
                                                                                                                                     (conv10$1_0 conv$1_0))
                                                                                                                                    (let
                                                                                                                                       ((cmp11$1_0 (= conv9$1_0 conv10$1_0)))
                                                                                                                                       (=>
                                                                                                                                          (not cmp11$1_0)
                                                                                                                                          (let
                                                                                                                                             ((_$1_3 (select HEAP$1 incdec.ptr$1_0)))
                                                                                                                                             (let
                                                                                                                                                ((conv15$1_0 _$1_3))
                                                                                                                                                (let
                                                                                                                                                   ((cmp16$1_0 (= conv15$1_0 0)))
                                                                                                                                                   (=>
                                                                                                                                                      (not cmp16$1_0)
                                                                                                                                                      (let
                                                                                                                                                         ((incdec.ptr21$1_0 (+ incdec.ptr$1_0 1)))
                                                                                                                                                         (let
                                                                                                                                                            ((_$1_4 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                                                                                            (let
                                                                                                                                                               ((conv22$1_0 _$1_4)
                                                                                                                                                                (conv23$1_0 conv$1_0))
                                                                                                                                                               (let
                                                                                                                                                                  ((cmp24$1_0 (= conv22$1_0 conv23$1_0)))
                                                                                                                                                                  (=>
                                                                                                                                                                     (not cmp24$1_0)
                                                                                                                                                                     (let
                                                                                                                                                                        ((_$1_5 (select HEAP$1 incdec.ptr21$1_0)))
                                                                                                                                                                        (let
                                                                                                                                                                           ((conv28$1_0 _$1_5))
                                                                                                                                                                           (let
                                                                                                                                                                              ((cmp29$1_0 (= conv28$1_0 0)))
                                                                                                                                                                              (=>
                                                                                                                                                                                 (not cmp29$1_0)
                                                                                                                                                                                 (let
                                                                                                                                                                                    ((incdec.ptr34$1_0 (+ incdec.ptr21$1_0 1)))
                                                                                                                                                                                    (let
                                                                                                                                                                                       ((_$1_6 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                                                                                                       (let
                                                                                                                                                                                          ((conv35$1_0 _$1_6)
                                                                                                                                                                                           (conv36$1_0 conv$1_0))
                                                                                                                                                                                          (let
                                                                                                                                                                                             ((cmp37$1_0 (= conv35$1_0 conv36$1_0)))
                                                                                                                                                                                             (=>
                                                                                                                                                                                                (not cmp37$1_0)
                                                                                                                                                                                                (let
                                                                                                                                                                                                   ((_$1_7 (select HEAP$1 incdec.ptr34$1_0)))
                                                                                                                                                                                                   (let
                                                                                                                                                                                                      ((conv41$1_0 _$1_7))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                         ((cmp42$1_0 (= conv41$1_0 0)))
                                                                                                                                                                                                         (=>
                                                                                                                                                                                                            (not cmp42$1_0)
                                                                                                                                                                                                            (let
                                                                                                                                                                                                               ((s.addr.0$1_0 incdec.ptr34$1_0))
                                                                                                                                                                                                               false))))))))))))))))))))))))))))))))))))))
                                                                                             (forall
                                                                                                ((i1_old Int)
                                                                                                 (i2 Int))
                                                                                                (INV_MAIN_42 conv$1_0_old s.addr.0$1_0_old i1_old (select HEAP$1_old i1_old) conv$2_0 t.addr.0$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))))
(check-sat)
(get-model)
