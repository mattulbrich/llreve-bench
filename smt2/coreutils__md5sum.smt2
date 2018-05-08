;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((s$1_0 Int)
    (s_len$1_0 Int)
    (hex_digest$1_0 Int)
    (file_name$1_0 Int)
    (HEAP$1 (Array Int Int))
    (s$2_0 Int)
    (s_len$2_0 Int)
    (hex_digest$2_0 Int)
    (file_name$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= s$1_0 s$2_0)
      (= s_len$1_0 s_len$2_0)
      (= hex_digest$1_0 hex_digest$2_0)
      (= file_name$1_0 file_name$2_0)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))
      (>= s$1_0 0)
      (>= hex_digest$1_0 0)
      (>= file_name$1_0 0)
      (>= s$2_0 0)
      (>= hex_digest$2_0 0)
      (>= file_name$2_0 0)
      (distinct s_len$1_0 0)))
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
; :annot (INV_MAIN_1 hex_digest$1_0 i.0$1_0 s$1_0 HEAP$1 hex_digest$2_0 i.0$2_0 s$2_0 HEAP$2)
(declare-fun
   INV_MAIN_1
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
; :annot (INV_MAIN_2 hex_digest$1_0 i.1$1_0 s$1_0 HEAP$1 hex_digest$2_0 i.1$2_0 s$2_0 HEAP$2)
(declare-fun
   INV_MAIN_2
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
; :annot (INV_MAIN_3 hex_digest$1_0 i.2.sink$1_0 s$1_0 HEAP$1 hex_digest$2_0 i.2.sink$2_0 s$2_0 HEAP$2)
(declare-fun
   INV_MAIN_3
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
      ((s$1_0_old Int)
       (s_len$1_0_old Int)
       (hex_digest$1_0_old Int)
       (file_name$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s$2_0_old Int)
       (s_len$2_0_old Int)
       (hex_digest$2_0_old Int)
       (file_name$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old s_len$1_0_old hex_digest$1_0_old file_name$1_0_old HEAP$1_old s$2_0_old s_len$2_0_old hex_digest$2_0_old file_name$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old)
             (s_len$1_0 s_len$1_0_old)
             (hex_digest$1_0 hex_digest$1_0_old)
             (file_name$1_0 file_name$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((HEAP$1 (store HEAP$1 file_name$1_0 s$1_0))
                (sub$1_0 (- s_len$1_0 1)))
               (let
                  ((i.0$1_0 sub$1_0)
                   (s$2_0 s$2_0_old)
                   (s_len$2_0 s_len$2_0_old))
                  (let
                     ((hex_digest$2_0 hex_digest$2_0_old)
                      (file_name$2_0 file_name$2_0_old)
                      (HEAP$2 HEAP$2_old)
                      (cmp$2_0 (= s_len$2_0 0)))
                     (=>
                        cmp$2_0
                        (let
                           ((retval.0$2_0 0))
                           (let
                              ((result$2 retval.0$2_0)
                               (HEAP$2_res HEAP$2))
                              false))))))))))
(assert
   (forall
      ((s$1_0_old Int)
       (s_len$1_0_old Int)
       (hex_digest$1_0_old Int)
       (file_name$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (s$2_0_old Int)
       (s_len$2_0_old Int)
       (hex_digest$2_0_old Int)
       (file_name$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV s$1_0_old s_len$1_0_old hex_digest$1_0_old file_name$1_0_old HEAP$1_old s$2_0_old s_len$2_0_old hex_digest$2_0_old file_name$2_0_old HEAP$2_old)
         (let
            ((s$1_0 s$1_0_old)
             (s_len$1_0 s_len$1_0_old)
             (hex_digest$1_0 hex_digest$1_0_old)
             (file_name$1_0 file_name$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((HEAP$1 (store HEAP$1 file_name$1_0 s$1_0))
                (sub$1_0 (- s_len$1_0 1)))
               (let
                  ((i.0$1_0 sub$1_0)
                   (s$2_0 s$2_0_old)
                   (s_len$2_0 s_len$2_0_old))
                  (let
                     ((hex_digest$2_0 hex_digest$2_0_old)
                      (file_name$2_0 file_name$2_0_old)
                      (HEAP$2 HEAP$2_old)
                      (cmp$2_0 (= s_len$2_0 0)))
                     (=>
                        (not cmp$2_0)
                        (let
                           ((HEAP$2 (store HEAP$2 file_name$2_0 s$2_0))
                            (sub$2_0 (- s_len$2_0 1)))
                           (let
                              ((i.0$2_0 sub$2_0))
                              (forall
                                 ((i1 Int)
                                  (i2 Int))
                                 (INV_MAIN_1 hex_digest$1_0 i.0$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.0$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  tobool$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((conv$1_0 _$1_0))
                              (let
                                 ((cmp$1_0 (distinct conv$1_0 41)))
                                 (let
                                    ((_$1_1 cmp$1_0))
                                    (=>
                                       (not _$1_1)
                                       (let
                                          ((idxprom3$1_0 i.0$1_0))
                                          (let
                                             ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                                             (let
                                                ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                                (let
                                                   ((conv5$1_0 _$1_2))
                                                   (let
                                                      ((cmp6$1_0 (distinct conv5$1_0 41)))
                                                      (=>
                                                         cmp6$1_0
                                                         (let
                                                            ((retval.0$1_0 0))
                                                            (let
                                                               ((result$1 retval.0$1_0)
                                                                (HEAP$1_res HEAP$1)
                                                                (hex_digest$2_0 hex_digest$2_0_old)
                                                                (i.0$2_0 i.0$2_0_old))
                                                               (let
                                                                  ((s$2_0 s$2_0_old)
                                                                   (HEAP$2 HEAP$2_old)
                                                                   (tobool$2_0 (distinct i.0$2_0 0)))
                                                                  (=>
                                                                     tobool$2_0
                                                                     (let
                                                                        ((idxprom$2_0 i.0$2_0))
                                                                        (let
                                                                           ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                                                                           (let
                                                                              ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                              (let
                                                                                 ((conv$2_0 _$2_0))
                                                                                 (let
                                                                                    ((cmp1$2_0 (distinct conv$2_0 41)))
                                                                                    (let
                                                                                       ((_$2_1 cmp1$2_0))
                                                                                       (=>
                                                                                          (not _$2_1)
                                                                                          (let
                                                                                             ((idxprom4$2_0 i.0$2_0))
                                                                                             (let
                                                                                                ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                                                (let
                                                                                                   ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                                   (let
                                                                                                      ((conv6$2_0 _$2_2))
                                                                                                      (let
                                                                                                         ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                                                         (=>
                                                                                                            (not cmp7$2_0)
                                                                                                            (let
                                                                                                               ((inc$2_0 (+ i.0$2_0 1))
                                                                                                                (idxprom11$2_0 i.0$2_0))
                                                                                                               (let
                                                                                                                  ((arrayidx12$2_0 (+ s$2_0 idxprom11$2_0)))
                                                                                                                  (let
                                                                                                                     ((HEAP$2 (store HEAP$2 arrayidx12$2_0 0))
                                                                                                                      (i.1$2_0 inc$2_0))
                                                                                                                     false)))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  tobool$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((conv$1_0 _$1_0))
                              (let
                                 ((cmp$1_0 (distinct conv$1_0 41)))
                                 (let
                                    ((_$1_1 cmp$1_0))
                                    (=>
                                       (not _$1_1)
                                       (let
                                          ((idxprom3$1_0 i.0$1_0))
                                          (let
                                             ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                                             (let
                                                ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                                (let
                                                   ((conv5$1_0 _$1_2))
                                                   (let
                                                      ((cmp6$1_0 (distinct conv5$1_0 41)))
                                                      (=>
                                                         cmp6$1_0
                                                         (let
                                                            ((retval.0$1_0 0))
                                                            (let
                                                               ((result$1 retval.0$1_0)
                                                                (HEAP$1_res HEAP$1)
                                                                (hex_digest$2_0 hex_digest$2_0_old)
                                                                (i.0$2_0 i.0$2_0_old))
                                                               (let
                                                                  ((s$2_0 s$2_0_old)
                                                                   (HEAP$2 HEAP$2_old)
                                                                   (tobool$2_0 (distinct i.0$2_0 0)))
                                                                  (=>
                                                                     (not tobool$2_0)
                                                                     (let
                                                                        ((_$2_1 false))
                                                                        (=>
                                                                           (not _$2_1)
                                                                           (let
                                                                              ((idxprom4$2_0 i.0$2_0))
                                                                              (let
                                                                                 ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                                 (let
                                                                                    ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                    (let
                                                                                       ((conv6$2_0 _$2_2))
                                                                                       (let
                                                                                          ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                                          (=>
                                                                                             (not cmp7$2_0)
                                                                                             (let
                                                                                                ((inc$2_0 (+ i.0$2_0 1))
                                                                                                 (idxprom11$2_0 i.0$2_0))
                                                                                                (let
                                                                                                   ((arrayidx12$2_0 (+ s$2_0 idxprom11$2_0)))
                                                                                                   (let
                                                                                                      ((HEAP$2 (store HEAP$2 arrayidx12$2_0 0))
                                                                                                       (i.1$2_0 inc$2_0))
                                                                                                      false))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  (not tobool$1_0)
                  (let
                     ((_$1_1 false))
                     (=>
                        (not _$1_1)
                        (let
                           ((idxprom3$1_0 i.0$1_0))
                           (let
                              ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                              (let
                                 ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                 (let
                                    ((conv5$1_0 _$1_2))
                                    (let
                                       ((cmp6$1_0 (distinct conv5$1_0 41)))
                                       (=>
                                          cmp6$1_0
                                          (let
                                             ((retval.0$1_0 0))
                                             (let
                                                ((result$1 retval.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (hex_digest$2_0 hex_digest$2_0_old)
                                                 (i.0$2_0 i.0$2_0_old))
                                                (let
                                                   ((s$2_0 s$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (tobool$2_0 (distinct i.0$2_0 0)))
                                                   (=>
                                                      tobool$2_0
                                                      (let
                                                         ((idxprom$2_0 i.0$2_0))
                                                         (let
                                                            ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                                                            (let
                                                               ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                               (let
                                                                  ((conv$2_0 _$2_0))
                                                                  (let
                                                                     ((cmp1$2_0 (distinct conv$2_0 41)))
                                                                     (let
                                                                        ((_$2_1 cmp1$2_0))
                                                                        (=>
                                                                           (not _$2_1)
                                                                           (let
                                                                              ((idxprom4$2_0 i.0$2_0))
                                                                              (let
                                                                                 ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                                 (let
                                                                                    ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                    (let
                                                                                       ((conv6$2_0 _$2_2))
                                                                                       (let
                                                                                          ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                                          (=>
                                                                                             (not cmp7$2_0)
                                                                                             (let
                                                                                                ((inc$2_0 (+ i.0$2_0 1))
                                                                                                 (idxprom11$2_0 i.0$2_0))
                                                                                                (let
                                                                                                   ((arrayidx12$2_0 (+ s$2_0 idxprom11$2_0)))
                                                                                                   (let
                                                                                                      ((HEAP$2 (store HEAP$2 arrayidx12$2_0 0))
                                                                                                       (i.1$2_0 inc$2_0))
                                                                                                      false))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  (not tobool$1_0)
                  (let
                     ((_$1_1 false))
                     (=>
                        (not _$1_1)
                        (let
                           ((idxprom3$1_0 i.0$1_0))
                           (let
                              ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                              (let
                                 ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                 (let
                                    ((conv5$1_0 _$1_2))
                                    (let
                                       ((cmp6$1_0 (distinct conv5$1_0 41)))
                                       (=>
                                          cmp6$1_0
                                          (let
                                             ((retval.0$1_0 0))
                                             (let
                                                ((result$1 retval.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (hex_digest$2_0 hex_digest$2_0_old)
                                                 (i.0$2_0 i.0$2_0_old))
                                                (let
                                                   ((s$2_0 s$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (tobool$2_0 (distinct i.0$2_0 0)))
                                                   (=>
                                                      (not tobool$2_0)
                                                      (let
                                                         ((_$2_1 false))
                                                         (=>
                                                            (not _$2_1)
                                                            (let
                                                               ((idxprom4$2_0 i.0$2_0))
                                                               (let
                                                                  ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                  (let
                                                                     ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                     (let
                                                                        ((conv6$2_0 _$2_2))
                                                                        (let
                                                                           ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                           (=>
                                                                              (not cmp7$2_0)
                                                                              (let
                                                                                 ((inc$2_0 (+ i.0$2_0 1))
                                                                                  (idxprom11$2_0 i.0$2_0))
                                                                                 (let
                                                                                    ((arrayidx12$2_0 (+ s$2_0 idxprom11$2_0)))
                                                                                    (let
                                                                                       ((HEAP$2 (store HEAP$2 arrayidx12$2_0 0))
                                                                                        (i.1$2_0 inc$2_0))
                                                                                       false)))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  tobool$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((conv$1_0 _$1_0))
                              (let
                                 ((cmp$1_0 (distinct conv$1_0 41)))
                                 (let
                                    ((_$1_1 cmp$1_0))
                                    (=>
                                       (not _$1_1)
                                       (let
                                          ((idxprom3$1_0 i.0$1_0))
                                          (let
                                             ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                                             (let
                                                ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                                (let
                                                   ((conv5$1_0 _$1_2))
                                                   (let
                                                      ((cmp6$1_0 (distinct conv5$1_0 41)))
                                                      (=>
                                                         (not cmp6$1_0)
                                                         (let
                                                            ((inc$1_0 (+ i.0$1_0 1))
                                                             (idxprom8$1_0 i.0$1_0))
                                                            (let
                                                               ((arrayidx9$1_0 (+ s$1_0 idxprom8$1_0)))
                                                               (let
                                                                  ((HEAP$1 (store HEAP$1 arrayidx9$1_0 0))
                                                                   (i.1$1_0 inc$1_0)
                                                                   (hex_digest$2_0 hex_digest$2_0_old)
                                                                   (i.0$2_0 i.0$2_0_old))
                                                                  (let
                                                                     ((s$2_0 s$2_0_old)
                                                                      (HEAP$2 HEAP$2_old)
                                                                      (tobool$2_0 (distinct i.0$2_0 0)))
                                                                     (=>
                                                                        tobool$2_0
                                                                        (let
                                                                           ((idxprom$2_0 i.0$2_0))
                                                                           (let
                                                                              ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                                                                              (let
                                                                                 ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                                 (let
                                                                                    ((conv$2_0 _$2_0))
                                                                                    (let
                                                                                       ((cmp1$2_0 (distinct conv$2_0 41)))
                                                                                       (let
                                                                                          ((_$2_1 cmp1$2_0))
                                                                                          (=>
                                                                                             (not _$2_1)
                                                                                             (let
                                                                                                ((idxprom4$2_0 i.0$2_0))
                                                                                                (let
                                                                                                   ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                                                   (let
                                                                                                      ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                                      (let
                                                                                                         ((conv6$2_0 _$2_2))
                                                                                                         (let
                                                                                                            ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                                                            (=>
                                                                                                               cmp7$2_0
                                                                                                               (let
                                                                                                                  ((retval.0$2_0 0))
                                                                                                                  (let
                                                                                                                     ((result$2 retval.0$2_0)
                                                                                                                      (HEAP$2_res HEAP$2))
                                                                                                                     false)))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  tobool$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((conv$1_0 _$1_0))
                              (let
                                 ((cmp$1_0 (distinct conv$1_0 41)))
                                 (let
                                    ((_$1_1 cmp$1_0))
                                    (=>
                                       (not _$1_1)
                                       (let
                                          ((idxprom3$1_0 i.0$1_0))
                                          (let
                                             ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                                             (let
                                                ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                                (let
                                                   ((conv5$1_0 _$1_2))
                                                   (let
                                                      ((cmp6$1_0 (distinct conv5$1_0 41)))
                                                      (=>
                                                         (not cmp6$1_0)
                                                         (let
                                                            ((inc$1_0 (+ i.0$1_0 1))
                                                             (idxprom8$1_0 i.0$1_0))
                                                            (let
                                                               ((arrayidx9$1_0 (+ s$1_0 idxprom8$1_0)))
                                                               (let
                                                                  ((HEAP$1 (store HEAP$1 arrayidx9$1_0 0))
                                                                   (i.1$1_0 inc$1_0)
                                                                   (hex_digest$2_0 hex_digest$2_0_old)
                                                                   (i.0$2_0 i.0$2_0_old))
                                                                  (let
                                                                     ((s$2_0 s$2_0_old)
                                                                      (HEAP$2 HEAP$2_old)
                                                                      (tobool$2_0 (distinct i.0$2_0 0)))
                                                                     (=>
                                                                        (not tobool$2_0)
                                                                        (let
                                                                           ((_$2_1 false))
                                                                           (=>
                                                                              (not _$2_1)
                                                                              (let
                                                                                 ((idxprom4$2_0 i.0$2_0))
                                                                                 (let
                                                                                    ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                                    (let
                                                                                       ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                       (let
                                                                                          ((conv6$2_0 _$2_2))
                                                                                          (let
                                                                                             ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                                             (=>
                                                                                                cmp7$2_0
                                                                                                (let
                                                                                                   ((retval.0$2_0 0))
                                                                                                   (let
                                                                                                      ((result$2 retval.0$2_0)
                                                                                                       (HEAP$2_res HEAP$2))
                                                                                                      false))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  (not tobool$1_0)
                  (let
                     ((_$1_1 false))
                     (=>
                        (not _$1_1)
                        (let
                           ((idxprom3$1_0 i.0$1_0))
                           (let
                              ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                              (let
                                 ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                 (let
                                    ((conv5$1_0 _$1_2))
                                    (let
                                       ((cmp6$1_0 (distinct conv5$1_0 41)))
                                       (=>
                                          (not cmp6$1_0)
                                          (let
                                             ((inc$1_0 (+ i.0$1_0 1))
                                              (idxprom8$1_0 i.0$1_0))
                                             (let
                                                ((arrayidx9$1_0 (+ s$1_0 idxprom8$1_0)))
                                                (let
                                                   ((HEAP$1 (store HEAP$1 arrayidx9$1_0 0))
                                                    (i.1$1_0 inc$1_0)
                                                    (hex_digest$2_0 hex_digest$2_0_old)
                                                    (i.0$2_0 i.0$2_0_old))
                                                   (let
                                                      ((s$2_0 s$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (tobool$2_0 (distinct i.0$2_0 0)))
                                                      (=>
                                                         tobool$2_0
                                                         (let
                                                            ((idxprom$2_0 i.0$2_0))
                                                            (let
                                                               ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                                                               (let
                                                                  ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                  (let
                                                                     ((conv$2_0 _$2_0))
                                                                     (let
                                                                        ((cmp1$2_0 (distinct conv$2_0 41)))
                                                                        (let
                                                                           ((_$2_1 cmp1$2_0))
                                                                           (=>
                                                                              (not _$2_1)
                                                                              (let
                                                                                 ((idxprom4$2_0 i.0$2_0))
                                                                                 (let
                                                                                    ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                                    (let
                                                                                       ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                       (let
                                                                                          ((conv6$2_0 _$2_2))
                                                                                          (let
                                                                                             ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                                             (=>
                                                                                                cmp7$2_0
                                                                                                (let
                                                                                                   ((retval.0$2_0 0))
                                                                                                   (let
                                                                                                      ((result$2 retval.0$2_0)
                                                                                                       (HEAP$2_res HEAP$2))
                                                                                                      false))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  (not tobool$1_0)
                  (let
                     ((_$1_1 false))
                     (=>
                        (not _$1_1)
                        (let
                           ((idxprom3$1_0 i.0$1_0))
                           (let
                              ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                              (let
                                 ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                 (let
                                    ((conv5$1_0 _$1_2))
                                    (let
                                       ((cmp6$1_0 (distinct conv5$1_0 41)))
                                       (=>
                                          (not cmp6$1_0)
                                          (let
                                             ((inc$1_0 (+ i.0$1_0 1))
                                              (idxprom8$1_0 i.0$1_0))
                                             (let
                                                ((arrayidx9$1_0 (+ s$1_0 idxprom8$1_0)))
                                                (let
                                                   ((HEAP$1 (store HEAP$1 arrayidx9$1_0 0))
                                                    (i.1$1_0 inc$1_0)
                                                    (hex_digest$2_0 hex_digest$2_0_old)
                                                    (i.0$2_0 i.0$2_0_old))
                                                   (let
                                                      ((s$2_0 s$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (tobool$2_0 (distinct i.0$2_0 0)))
                                                      (=>
                                                         (not tobool$2_0)
                                                         (let
                                                            ((_$2_1 false))
                                                            (=>
                                                               (not _$2_1)
                                                               (let
                                                                  ((idxprom4$2_0 i.0$2_0))
                                                                  (let
                                                                     ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                     (let
                                                                        ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                        (let
                                                                           ((conv6$2_0 _$2_2))
                                                                           (let
                                                                              ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                              (=>
                                                                                 cmp7$2_0
                                                                                 (let
                                                                                    ((retval.0$2_0 0))
                                                                                    (let
                                                                                       ((result$2 retval.0$2_0)
                                                                                        (HEAP$2_res HEAP$2))
                                                                                       false)))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  tobool$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((conv$1_0 _$1_0))
                              (let
                                 ((cmp$1_0 (distinct conv$1_0 41)))
                                 (let
                                    ((_$1_1 cmp$1_0))
                                    (=>
                                       (not _$1_1)
                                       (let
                                          ((idxprom3$1_0 i.0$1_0))
                                          (let
                                             ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                                             (let
                                                ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                                (let
                                                   ((conv5$1_0 _$1_2))
                                                   (let
                                                      ((cmp6$1_0 (distinct conv5$1_0 41)))
                                                      (=>
                                                         cmp6$1_0
                                                         (let
                                                            ((retval.0$1_0 0))
                                                            (let
                                                               ((result$1 retval.0$1_0)
                                                                (HEAP$1_res HEAP$1)
                                                                (hex_digest$2_0 hex_digest$2_0_old)
                                                                (i.0$2_0 i.0$2_0_old))
                                                               (let
                                                                  ((s$2_0 s$2_0_old)
                                                                   (HEAP$2 HEAP$2_old)
                                                                   (tobool$2_0 (distinct i.0$2_0 0)))
                                                                  (=>
                                                                     tobool$2_0
                                                                     (let
                                                                        ((idxprom$2_0 i.0$2_0))
                                                                        (let
                                                                           ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                                                                           (let
                                                                              ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                              (let
                                                                                 ((conv$2_0 _$2_0))
                                                                                 (let
                                                                                    ((cmp1$2_0 (distinct conv$2_0 41)))
                                                                                    (let
                                                                                       ((_$2_1 cmp1$2_0))
                                                                                       (=>
                                                                                          (not _$2_1)
                                                                                          (let
                                                                                             ((idxprom4$2_0 i.0$2_0))
                                                                                             (let
                                                                                                ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                                                (let
                                                                                                   ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                                   (let
                                                                                                      ((conv6$2_0 _$2_2))
                                                                                                      (let
                                                                                                         ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                                                         (=>
                                                                                                            cmp7$2_0
                                                                                                            (let
                                                                                                               ((retval.0$2_0 0))
                                                                                                               (let
                                                                                                                  ((result$2 retval.0$2_0)
                                                                                                                   (HEAP$2_res HEAP$2))
                                                                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  tobool$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((conv$1_0 _$1_0))
                              (let
                                 ((cmp$1_0 (distinct conv$1_0 41)))
                                 (let
                                    ((_$1_1 cmp$1_0))
                                    (=>
                                       (not _$1_1)
                                       (let
                                          ((idxprom3$1_0 i.0$1_0))
                                          (let
                                             ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                                             (let
                                                ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                                (let
                                                   ((conv5$1_0 _$1_2))
                                                   (let
                                                      ((cmp6$1_0 (distinct conv5$1_0 41)))
                                                      (=>
                                                         cmp6$1_0
                                                         (let
                                                            ((retval.0$1_0 0))
                                                            (let
                                                               ((result$1 retval.0$1_0)
                                                                (HEAP$1_res HEAP$1)
                                                                (hex_digest$2_0 hex_digest$2_0_old)
                                                                (i.0$2_0 i.0$2_0_old))
                                                               (let
                                                                  ((s$2_0 s$2_0_old)
                                                                   (HEAP$2 HEAP$2_old)
                                                                   (tobool$2_0 (distinct i.0$2_0 0)))
                                                                  (=>
                                                                     (not tobool$2_0)
                                                                     (let
                                                                        ((_$2_1 false))
                                                                        (=>
                                                                           (not _$2_1)
                                                                           (let
                                                                              ((idxprom4$2_0 i.0$2_0))
                                                                              (let
                                                                                 ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                                 (let
                                                                                    ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                    (let
                                                                                       ((conv6$2_0 _$2_2))
                                                                                       (let
                                                                                          ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                                          (=>
                                                                                             cmp7$2_0
                                                                                             (let
                                                                                                ((retval.0$2_0 0))
                                                                                                (let
                                                                                                   ((result$2 retval.0$2_0)
                                                                                                    (HEAP$2_res HEAP$2))
                                                                                                   (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  (not tobool$1_0)
                  (let
                     ((_$1_1 false))
                     (=>
                        (not _$1_1)
                        (let
                           ((idxprom3$1_0 i.0$1_0))
                           (let
                              ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                              (let
                                 ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                 (let
                                    ((conv5$1_0 _$1_2))
                                    (let
                                       ((cmp6$1_0 (distinct conv5$1_0 41)))
                                       (=>
                                          cmp6$1_0
                                          (let
                                             ((retval.0$1_0 0))
                                             (let
                                                ((result$1 retval.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (hex_digest$2_0 hex_digest$2_0_old)
                                                 (i.0$2_0 i.0$2_0_old))
                                                (let
                                                   ((s$2_0 s$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (tobool$2_0 (distinct i.0$2_0 0)))
                                                   (=>
                                                      tobool$2_0
                                                      (let
                                                         ((idxprom$2_0 i.0$2_0))
                                                         (let
                                                            ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                                                            (let
                                                               ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                               (let
                                                                  ((conv$2_0 _$2_0))
                                                                  (let
                                                                     ((cmp1$2_0 (distinct conv$2_0 41)))
                                                                     (let
                                                                        ((_$2_1 cmp1$2_0))
                                                                        (=>
                                                                           (not _$2_1)
                                                                           (let
                                                                              ((idxprom4$2_0 i.0$2_0))
                                                                              (let
                                                                                 ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                                 (let
                                                                                    ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                    (let
                                                                                       ((conv6$2_0 _$2_2))
                                                                                       (let
                                                                                          ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                                          (=>
                                                                                             cmp7$2_0
                                                                                             (let
                                                                                                ((retval.0$2_0 0))
                                                                                                (let
                                                                                                   ((result$2 retval.0$2_0)
                                                                                                    (HEAP$2_res HEAP$2))
                                                                                                   (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  (not tobool$1_0)
                  (let
                     ((_$1_1 false))
                     (=>
                        (not _$1_1)
                        (let
                           ((idxprom3$1_0 i.0$1_0))
                           (let
                              ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                              (let
                                 ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                 (let
                                    ((conv5$1_0 _$1_2))
                                    (let
                                       ((cmp6$1_0 (distinct conv5$1_0 41)))
                                       (=>
                                          cmp6$1_0
                                          (let
                                             ((retval.0$1_0 0))
                                             (let
                                                ((result$1 retval.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (hex_digest$2_0 hex_digest$2_0_old)
                                                 (i.0$2_0 i.0$2_0_old))
                                                (let
                                                   ((s$2_0 s$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (tobool$2_0 (distinct i.0$2_0 0)))
                                                   (=>
                                                      (not tobool$2_0)
                                                      (let
                                                         ((_$2_1 false))
                                                         (=>
                                                            (not _$2_1)
                                                            (let
                                                               ((idxprom4$2_0 i.0$2_0))
                                                               (let
                                                                  ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                  (let
                                                                     ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                     (let
                                                                        ((conv6$2_0 _$2_2))
                                                                        (let
                                                                           ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                           (=>
                                                                              cmp7$2_0
                                                                              (let
                                                                                 ((retval.0$2_0 0))
                                                                                 (let
                                                                                    ((result$2 retval.0$2_0)
                                                                                     (HEAP$2_res HEAP$2))
                                                                                    (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  tobool$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((conv$1_0 _$1_0))
                              (let
                                 ((cmp$1_0 (distinct conv$1_0 41)))
                                 (let
                                    ((_$1_1 cmp$1_0))
                                    (=>
                                       _$1_1
                                       (let
                                          ((dec$1_0 (+ i.0$1_0 (- 1))))
                                          (let
                                             ((i.0$1_0 dec$1_0)
                                              (hex_digest$2_0 hex_digest$2_0_old)
                                              (i.0$2_0 i.0$2_0_old))
                                             (let
                                                ((s$2_0 s$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (tobool$2_0 (distinct i.0$2_0 0)))
                                                (=>
                                                   tobool$2_0
                                                   (let
                                                      ((idxprom$2_0 i.0$2_0))
                                                      (let
                                                         ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                                                         (let
                                                            ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                            (let
                                                               ((conv$2_0 _$2_0))
                                                               (let
                                                                  ((cmp1$2_0 (distinct conv$2_0 41)))
                                                                  (let
                                                                     ((_$2_1 cmp1$2_0))
                                                                     (=>
                                                                        _$2_1
                                                                        (let
                                                                           ((dec$2_0 (+ i.0$2_0 (- 1))))
                                                                           (let
                                                                              ((i.0$2_0 dec$2_0))
                                                                              (forall
                                                                                 ((i1 Int)
                                                                                  (i2 Int))
                                                                                 (INV_MAIN_1 hex_digest$1_0 i.0$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.0$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  tobool$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((conv$1_0 _$1_0))
                              (let
                                 ((cmp$1_0 (distinct conv$1_0 41)))
                                 (let
                                    ((_$1_1 cmp$1_0))
                                    (=>
                                       _$1_1
                                       (let
                                          ((dec$1_0 (+ i.0$1_0 (- 1))))
                                          (let
                                             ((i.0$1_0 dec$1_0)
                                              (hex_digest$2_0 hex_digest$2_0_old)
                                              (i.0$2_0 i.0$2_0_old))
                                             (let
                                                ((s$2_0 s$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (tobool$2_0 (distinct i.0$2_0 0)))
                                                (=>
                                                   (not tobool$2_0)
                                                   (let
                                                      ((_$2_1 false))
                                                      (=>
                                                         _$2_1
                                                         (let
                                                            ((dec$2_0 (+ i.0$2_0 (- 1))))
                                                            (let
                                                               ((i.0$2_0 dec$2_0))
                                                               (forall
                                                                  ((i1 Int)
                                                                   (i2 Int))
                                                                  (INV_MAIN_1 hex_digest$1_0 i.0$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.0$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  (not tobool$1_0)
                  (let
                     ((_$1_1 false))
                     (=>
                        _$1_1
                        (let
                           ((dec$1_0 (+ i.0$1_0 (- 1))))
                           (let
                              ((i.0$1_0 dec$1_0)
                               (hex_digest$2_0 hex_digest$2_0_old)
                               (i.0$2_0 i.0$2_0_old))
                              (let
                                 ((s$2_0 s$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (tobool$2_0 (distinct i.0$2_0 0)))
                                 (=>
                                    tobool$2_0
                                    (let
                                       ((idxprom$2_0 i.0$2_0))
                                       (let
                                          ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                                          (let
                                             ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                             (let
                                                ((conv$2_0 _$2_0))
                                                (let
                                                   ((cmp1$2_0 (distinct conv$2_0 41)))
                                                   (let
                                                      ((_$2_1 cmp1$2_0))
                                                      (=>
                                                         _$2_1
                                                         (let
                                                            ((dec$2_0 (+ i.0$2_0 (- 1))))
                                                            (let
                                                               ((i.0$2_0 dec$2_0))
                                                               (forall
                                                                  ((i1 Int)
                                                                   (i2 Int))
                                                                  (INV_MAIN_1 hex_digest$1_0 i.0$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.0$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  (not tobool$1_0)
                  (let
                     ((_$1_1 false))
                     (=>
                        _$1_1
                        (let
                           ((dec$1_0 (+ i.0$1_0 (- 1))))
                           (let
                              ((i.0$1_0 dec$1_0)
                               (hex_digest$2_0 hex_digest$2_0_old)
                               (i.0$2_0 i.0$2_0_old))
                              (let
                                 ((s$2_0 s$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (tobool$2_0 (distinct i.0$2_0 0)))
                                 (=>
                                    (not tobool$2_0)
                                    (let
                                       ((_$2_1 false))
                                       (=>
                                          _$2_1
                                          (let
                                             ((dec$2_0 (+ i.0$2_0 (- 1))))
                                             (let
                                                ((i.0$2_0 dec$2_0))
                                                (forall
                                                   ((i1 Int)
                                                    (i2 Int))
                                                   (INV_MAIN_1 hex_digest$1_0 i.0$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.0$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  tobool$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((conv$1_0 _$1_0))
                              (let
                                 ((cmp$1_0 (distinct conv$1_0 41)))
                                 (let
                                    ((_$1_1 cmp$1_0))
                                    (=>
                                       _$1_1
                                       (let
                                          ((dec$1_0 (+ i.0$1_0 (- 1))))
                                          (let
                                             ((i.0$1_0 dec$1_0))
                                             (=>
                                                (and
                                                   (let
                                                      ((hex_digest$2_0 hex_digest$2_0_old)
                                                       (i.0$2_0 i.0$2_0_old))
                                                      (let
                                                         ((s$2_0 s$2_0_old)
                                                          (HEAP$2 HEAP$2_old)
                                                          (tobool$2_0 (distinct i.0$2_0 0)))
                                                         (=>
                                                            tobool$2_0
                                                            (let
                                                               ((idxprom$2_0 i.0$2_0))
                                                               (let
                                                                  ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                                                                  (let
                                                                     ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                     (let
                                                                        ((conv$2_0 _$2_0))
                                                                        (let
                                                                           ((cmp1$2_0 (distinct conv$2_0 41)))
                                                                           (let
                                                                              ((_$2_1 cmp1$2_0))
                                                                              (=>
                                                                                 _$2_1
                                                                                 (let
                                                                                    ((dec$2_0 (+ i.0$2_0 (- 1))))
                                                                                    (let
                                                                                       ((i.0$2_0 dec$2_0))
                                                                                       false))))))))))))
                                                   (let
                                                      ((hex_digest$2_0 hex_digest$2_0_old)
                                                       (i.0$2_0 i.0$2_0_old))
                                                      (let
                                                         ((s$2_0 s$2_0_old)
                                                          (HEAP$2 HEAP$2_old)
                                                          (tobool$2_0 (distinct i.0$2_0 0)))
                                                         (=>
                                                            (not tobool$2_0)
                                                            (let
                                                               ((_$2_1 false))
                                                               (=>
                                                                  _$2_1
                                                                  (let
                                                                     ((dec$2_0 (+ i.0$2_0 (- 1))))
                                                                     (let
                                                                        ((i.0$2_0 dec$2_0))
                                                                        false))))))))
                                                (forall
                                                   ((i1 Int)
                                                    (i2_old Int))
                                                   (INV_MAIN_1 hex_digest$1_0 i.0$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  (not tobool$1_0)
                  (let
                     ((_$1_1 false))
                     (=>
                        _$1_1
                        (let
                           ((dec$1_0 (+ i.0$1_0 (- 1))))
                           (let
                              ((i.0$1_0 dec$1_0))
                              (=>
                                 (and
                                    (let
                                       ((hex_digest$2_0 hex_digest$2_0_old)
                                        (i.0$2_0 i.0$2_0_old))
                                       (let
                                          ((s$2_0 s$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (tobool$2_0 (distinct i.0$2_0 0)))
                                          (=>
                                             tobool$2_0
                                             (let
                                                ((idxprom$2_0 i.0$2_0))
                                                (let
                                                   ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                                                   (let
                                                      ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                      (let
                                                         ((conv$2_0 _$2_0))
                                                         (let
                                                            ((cmp1$2_0 (distinct conv$2_0 41)))
                                                            (let
                                                               ((_$2_1 cmp1$2_0))
                                                               (=>
                                                                  _$2_1
                                                                  (let
                                                                     ((dec$2_0 (+ i.0$2_0 (- 1))))
                                                                     (let
                                                                        ((i.0$2_0 dec$2_0))
                                                                        false))))))))))))
                                    (let
                                       ((hex_digest$2_0 hex_digest$2_0_old)
                                        (i.0$2_0 i.0$2_0_old))
                                       (let
                                          ((s$2_0 s$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (tobool$2_0 (distinct i.0$2_0 0)))
                                          (=>
                                             (not tobool$2_0)
                                             (let
                                                ((_$2_1 false))
                                                (=>
                                                   _$2_1
                                                   (let
                                                      ((dec$2_0 (+ i.0$2_0 (- 1))))
                                                      (let
                                                         ((i.0$2_0 dec$2_0))
                                                         false))))))))
                                 (forall
                                    ((i1 Int)
                                     (i2_old Int))
                                    (INV_MAIN_1 hex_digest$1_0 i.0$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$2_0 hex_digest$2_0_old)
             (i.0$2_0 i.0$2_0_old))
            (let
               ((s$2_0 s$2_0_old)
                (HEAP$2 HEAP$2_old)
                (tobool$2_0 (distinct i.0$2_0 0)))
               (=>
                  tobool$2_0
                  (let
                     ((idxprom$2_0 i.0$2_0))
                     (let
                        ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                        (let
                           ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                           (let
                              ((conv$2_0 _$2_0))
                              (let
                                 ((cmp1$2_0 (distinct conv$2_0 41)))
                                 (let
                                    ((_$2_1 cmp1$2_0))
                                    (=>
                                       _$2_1
                                       (let
                                          ((dec$2_0 (+ i.0$2_0 (- 1))))
                                          (let
                                             ((i.0$2_0 dec$2_0))
                                             (=>
                                                (and
                                                   (let
                                                      ((hex_digest$1_0 hex_digest$1_0_old)
                                                       (i.0$1_0 i.0$1_0_old))
                                                      (let
                                                         ((s$1_0 s$1_0_old)
                                                          (HEAP$1 HEAP$1_old)
                                                          (tobool$1_0 (distinct i.0$1_0 0)))
                                                         (=>
                                                            tobool$1_0
                                                            (let
                                                               ((idxprom$1_0 i.0$1_0))
                                                               (let
                                                                  ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                                                                  (let
                                                                     ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                                                     (let
                                                                        ((conv$1_0 _$1_0))
                                                                        (let
                                                                           ((cmp$1_0 (distinct conv$1_0 41)))
                                                                           (let
                                                                              ((_$1_1 cmp$1_0))
                                                                              (=>
                                                                                 _$1_1
                                                                                 (let
                                                                                    ((dec$1_0 (+ i.0$1_0 (- 1))))
                                                                                    (let
                                                                                       ((i.0$1_0 dec$1_0))
                                                                                       false))))))))))))
                                                   (let
                                                      ((hex_digest$1_0 hex_digest$1_0_old)
                                                       (i.0$1_0 i.0$1_0_old))
                                                      (let
                                                         ((s$1_0 s$1_0_old)
                                                          (HEAP$1 HEAP$1_old)
                                                          (tobool$1_0 (distinct i.0$1_0 0)))
                                                         (=>
                                                            (not tobool$1_0)
                                                            (let
                                                               ((_$1_1 false))
                                                               (=>
                                                                  _$1_1
                                                                  (let
                                                                     ((dec$1_0 (+ i.0$1_0 (- 1))))
                                                                     (let
                                                                        ((i.0$1_0 dec$1_0))
                                                                        false))))))))
                                                (forall
                                                   ((i1_old Int)
                                                    (i2 Int))
                                                   (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0 i.0$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$2_0 hex_digest$2_0_old)
             (i.0$2_0 i.0$2_0_old))
            (let
               ((s$2_0 s$2_0_old)
                (HEAP$2 HEAP$2_old)
                (tobool$2_0 (distinct i.0$2_0 0)))
               (=>
                  (not tobool$2_0)
                  (let
                     ((_$2_1 false))
                     (=>
                        _$2_1
                        (let
                           ((dec$2_0 (+ i.0$2_0 (- 1))))
                           (let
                              ((i.0$2_0 dec$2_0))
                              (=>
                                 (and
                                    (let
                                       ((hex_digest$1_0 hex_digest$1_0_old)
                                        (i.0$1_0 i.0$1_0_old))
                                       (let
                                          ((s$1_0 s$1_0_old)
                                           (HEAP$1 HEAP$1_old)
                                           (tobool$1_0 (distinct i.0$1_0 0)))
                                          (=>
                                             tobool$1_0
                                             (let
                                                ((idxprom$1_0 i.0$1_0))
                                                (let
                                                   ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                                                   (let
                                                      ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                                                      (let
                                                         ((conv$1_0 _$1_0))
                                                         (let
                                                            ((cmp$1_0 (distinct conv$1_0 41)))
                                                            (let
                                                               ((_$1_1 cmp$1_0))
                                                               (=>
                                                                  _$1_1
                                                                  (let
                                                                     ((dec$1_0 (+ i.0$1_0 (- 1))))
                                                                     (let
                                                                        ((i.0$1_0 dec$1_0))
                                                                        false))))))))))))
                                    (let
                                       ((hex_digest$1_0 hex_digest$1_0_old)
                                        (i.0$1_0 i.0$1_0_old))
                                       (let
                                          ((s$1_0 s$1_0_old)
                                           (HEAP$1 HEAP$1_old)
                                           (tobool$1_0 (distinct i.0$1_0 0)))
                                          (=>
                                             (not tobool$1_0)
                                             (let
                                                ((_$1_1 false))
                                                (=>
                                                   _$1_1
                                                   (let
                                                      ((dec$1_0 (+ i.0$1_0 (- 1))))
                                                      (let
                                                         ((i.0$1_0 dec$1_0))
                                                         false))))))))
                                 (forall
                                    ((i1_old Int)
                                     (i2 Int))
                                    (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0 i.0$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  tobool$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((conv$1_0 _$1_0))
                              (let
                                 ((cmp$1_0 (distinct conv$1_0 41)))
                                 (let
                                    ((_$1_1 cmp$1_0))
                                    (=>
                                       (not _$1_1)
                                       (let
                                          ((idxprom3$1_0 i.0$1_0))
                                          (let
                                             ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                                             (let
                                                ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                                (let
                                                   ((conv5$1_0 _$1_2))
                                                   (let
                                                      ((cmp6$1_0 (distinct conv5$1_0 41)))
                                                      (=>
                                                         (not cmp6$1_0)
                                                         (let
                                                            ((inc$1_0 (+ i.0$1_0 1))
                                                             (idxprom8$1_0 i.0$1_0))
                                                            (let
                                                               ((arrayidx9$1_0 (+ s$1_0 idxprom8$1_0)))
                                                               (let
                                                                  ((HEAP$1 (store HEAP$1 arrayidx9$1_0 0))
                                                                   (i.1$1_0 inc$1_0)
                                                                   (hex_digest$2_0 hex_digest$2_0_old)
                                                                   (i.0$2_0 i.0$2_0_old))
                                                                  (let
                                                                     ((s$2_0 s$2_0_old)
                                                                      (HEAP$2 HEAP$2_old)
                                                                      (tobool$2_0 (distinct i.0$2_0 0)))
                                                                     (=>
                                                                        tobool$2_0
                                                                        (let
                                                                           ((idxprom$2_0 i.0$2_0))
                                                                           (let
                                                                              ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                                                                              (let
                                                                                 ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                                 (let
                                                                                    ((conv$2_0 _$2_0))
                                                                                    (let
                                                                                       ((cmp1$2_0 (distinct conv$2_0 41)))
                                                                                       (let
                                                                                          ((_$2_1 cmp1$2_0))
                                                                                          (=>
                                                                                             (not _$2_1)
                                                                                             (let
                                                                                                ((idxprom4$2_0 i.0$2_0))
                                                                                                (let
                                                                                                   ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                                                   (let
                                                                                                      ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                                      (let
                                                                                                         ((conv6$2_0 _$2_2))
                                                                                                         (let
                                                                                                            ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                                                            (=>
                                                                                                               (not cmp7$2_0)
                                                                                                               (let
                                                                                                                  ((inc$2_0 (+ i.0$2_0 1))
                                                                                                                   (idxprom11$2_0 i.0$2_0))
                                                                                                                  (let
                                                                                                                     ((arrayidx12$2_0 (+ s$2_0 idxprom11$2_0)))
                                                                                                                     (let
                                                                                                                        ((HEAP$2 (store HEAP$2 arrayidx12$2_0 0))
                                                                                                                         (i.1$2_0 inc$2_0))
                                                                                                                        (forall
                                                                                                                           ((i1 Int)
                                                                                                                            (i2 Int))
                                                                                                                           (INV_MAIN_2 hex_digest$1_0 i.1$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.1$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  tobool$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ s$1_0 idxprom$1_0)))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0)))
                           (let
                              ((conv$1_0 _$1_0))
                              (let
                                 ((cmp$1_0 (distinct conv$1_0 41)))
                                 (let
                                    ((_$1_1 cmp$1_0))
                                    (=>
                                       (not _$1_1)
                                       (let
                                          ((idxprom3$1_0 i.0$1_0))
                                          (let
                                             ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                                             (let
                                                ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                                (let
                                                   ((conv5$1_0 _$1_2))
                                                   (let
                                                      ((cmp6$1_0 (distinct conv5$1_0 41)))
                                                      (=>
                                                         (not cmp6$1_0)
                                                         (let
                                                            ((inc$1_0 (+ i.0$1_0 1))
                                                             (idxprom8$1_0 i.0$1_0))
                                                            (let
                                                               ((arrayidx9$1_0 (+ s$1_0 idxprom8$1_0)))
                                                               (let
                                                                  ((HEAP$1 (store HEAP$1 arrayidx9$1_0 0))
                                                                   (i.1$1_0 inc$1_0)
                                                                   (hex_digest$2_0 hex_digest$2_0_old)
                                                                   (i.0$2_0 i.0$2_0_old))
                                                                  (let
                                                                     ((s$2_0 s$2_0_old)
                                                                      (HEAP$2 HEAP$2_old)
                                                                      (tobool$2_0 (distinct i.0$2_0 0)))
                                                                     (=>
                                                                        (not tobool$2_0)
                                                                        (let
                                                                           ((_$2_1 false))
                                                                           (=>
                                                                              (not _$2_1)
                                                                              (let
                                                                                 ((idxprom4$2_0 i.0$2_0))
                                                                                 (let
                                                                                    ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                                    (let
                                                                                       ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                       (let
                                                                                          ((conv6$2_0 _$2_2))
                                                                                          (let
                                                                                             ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                                             (=>
                                                                                                (not cmp7$2_0)
                                                                                                (let
                                                                                                   ((inc$2_0 (+ i.0$2_0 1))
                                                                                                    (idxprom11$2_0 i.0$2_0))
                                                                                                   (let
                                                                                                      ((arrayidx12$2_0 (+ s$2_0 idxprom11$2_0)))
                                                                                                      (let
                                                                                                         ((HEAP$2 (store HEAP$2 arrayidx12$2_0 0))
                                                                                                          (i.1$2_0 inc$2_0))
                                                                                                         (forall
                                                                                                            ((i1 Int)
                                                                                                             (i2 Int))
                                                                                                            (INV_MAIN_2 hex_digest$1_0 i.1$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.1$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  (not tobool$1_0)
                  (let
                     ((_$1_1 false))
                     (=>
                        (not _$1_1)
                        (let
                           ((idxprom3$1_0 i.0$1_0))
                           (let
                              ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                              (let
                                 ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                 (let
                                    ((conv5$1_0 _$1_2))
                                    (let
                                       ((cmp6$1_0 (distinct conv5$1_0 41)))
                                       (=>
                                          (not cmp6$1_0)
                                          (let
                                             ((inc$1_0 (+ i.0$1_0 1))
                                              (idxprom8$1_0 i.0$1_0))
                                             (let
                                                ((arrayidx9$1_0 (+ s$1_0 idxprom8$1_0)))
                                                (let
                                                   ((HEAP$1 (store HEAP$1 arrayidx9$1_0 0))
                                                    (i.1$1_0 inc$1_0)
                                                    (hex_digest$2_0 hex_digest$2_0_old)
                                                    (i.0$2_0 i.0$2_0_old))
                                                   (let
                                                      ((s$2_0 s$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (tobool$2_0 (distinct i.0$2_0 0)))
                                                      (=>
                                                         tobool$2_0
                                                         (let
                                                            ((idxprom$2_0 i.0$2_0))
                                                            (let
                                                               ((arrayidx$2_0 (+ s$2_0 idxprom$2_0)))
                                                               (let
                                                                  ((_$2_0 (select HEAP$2 arrayidx$2_0)))
                                                                  (let
                                                                     ((conv$2_0 _$2_0))
                                                                     (let
                                                                        ((cmp1$2_0 (distinct conv$2_0 41)))
                                                                        (let
                                                                           ((_$2_1 cmp1$2_0))
                                                                           (=>
                                                                              (not _$2_1)
                                                                              (let
                                                                                 ((idxprom4$2_0 i.0$2_0))
                                                                                 (let
                                                                                    ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                                    (let
                                                                                       ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                                       (let
                                                                                          ((conv6$2_0 _$2_2))
                                                                                          (let
                                                                                             ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                                             (=>
                                                                                                (not cmp7$2_0)
                                                                                                (let
                                                                                                   ((inc$2_0 (+ i.0$2_0 1))
                                                                                                    (idxprom11$2_0 i.0$2_0))
                                                                                                   (let
                                                                                                      ((arrayidx12$2_0 (+ s$2_0 idxprom11$2_0)))
                                                                                                      (let
                                                                                                         ((HEAP$2 (store HEAP$2 arrayidx12$2_0 0))
                                                                                                          (i.1$2_0 inc$2_0))
                                                                                                         (forall
                                                                                                            ((i1 Int)
                                                                                                             (i2 Int))
                                                                                                            (INV_MAIN_2 hex_digest$1_0 i.1$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.1$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.0$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.0$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_1 hex_digest$1_0_old i.0$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.0$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (tobool$1_0 (distinct i.0$1_0 0)))
               (=>
                  (not tobool$1_0)
                  (let
                     ((_$1_1 false))
                     (=>
                        (not _$1_1)
                        (let
                           ((idxprom3$1_0 i.0$1_0))
                           (let
                              ((arrayidx4$1_0 (+ s$1_0 idxprom3$1_0)))
                              (let
                                 ((_$1_2 (select HEAP$1 arrayidx4$1_0)))
                                 (let
                                    ((conv5$1_0 _$1_2))
                                    (let
                                       ((cmp6$1_0 (distinct conv5$1_0 41)))
                                       (=>
                                          (not cmp6$1_0)
                                          (let
                                             ((inc$1_0 (+ i.0$1_0 1))
                                              (idxprom8$1_0 i.0$1_0))
                                             (let
                                                ((arrayidx9$1_0 (+ s$1_0 idxprom8$1_0)))
                                                (let
                                                   ((HEAP$1 (store HEAP$1 arrayidx9$1_0 0))
                                                    (i.1$1_0 inc$1_0)
                                                    (hex_digest$2_0 hex_digest$2_0_old)
                                                    (i.0$2_0 i.0$2_0_old))
                                                   (let
                                                      ((s$2_0 s$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (tobool$2_0 (distinct i.0$2_0 0)))
                                                      (=>
                                                         (not tobool$2_0)
                                                         (let
                                                            ((_$2_1 false))
                                                            (=>
                                                               (not _$2_1)
                                                               (let
                                                                  ((idxprom4$2_0 i.0$2_0))
                                                                  (let
                                                                     ((arrayidx5$2_0 (+ s$2_0 idxprom4$2_0)))
                                                                     (let
                                                                        ((_$2_2 (select HEAP$2 arrayidx5$2_0)))
                                                                        (let
                                                                           ((conv6$2_0 _$2_2))
                                                                           (let
                                                                              ((cmp7$2_0 (distinct conv6$2_0 41)))
                                                                              (=>
                                                                                 (not cmp7$2_0)
                                                                                 (let
                                                                                    ((inc$2_0 (+ i.0$2_0 1))
                                                                                     (idxprom11$2_0 i.0$2_0))
                                                                                    (let
                                                                                       ((arrayidx12$2_0 (+ s$2_0 idxprom11$2_0)))
                                                                                       (let
                                                                                          ((HEAP$2 (store HEAP$2 arrayidx12$2_0 0))
                                                                                           (i.1$2_0 inc$2_0))
                                                                                          (forall
                                                                                             ((i1 Int)
                                                                                              (i2 Int))
                                                                                             (INV_MAIN_2 hex_digest$1_0 i.1$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.1$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              cmp15$1_0
                              (let
                                 ((_$1_5 true))
                                 (=>
                                    (not _$1_5)
                                    (let
                                       ((idxprom27$1_0 i.1$1_0))
                                       (let
                                          ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                          (let
                                             ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                             (let
                                                ((conv29$1_0 _$1_6))
                                                (let
                                                   ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                   (=>
                                                      cmp30$1_0
                                                      (let
                                                         ((retval.0$1_0 0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (hex_digest$2_0 hex_digest$2_0_old)
                                                             (i.1$2_0 i.1$2_0_old))
                                                            (let
                                                               ((s$2_0 s$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (idxprom15$2_0 i.1$2_0))
                                                               (let
                                                                  ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                  (let
                                                                     ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                     (let
                                                                        ((conv17$2_0 _$2_3))
                                                                        (let
                                                                           ((cmp18$2_0 (= conv17$2_0 32)))
                                                                           (=>
                                                                              cmp18$2_0
                                                                              (let
                                                                                 ((_$2_5 true))
                                                                                 (=>
                                                                                    (not _$2_5)
                                                                                    (let
                                                                                       ((idxprom30$2_0 i.1$2_0))
                                                                                       (let
                                                                                          ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                          (let
                                                                                             ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                             (let
                                                                                                ((conv32$2_0 _$2_6))
                                                                                                (let
                                                                                                   ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                   (=>
                                                                                                      (not cmp33$2_0)
                                                                                                      (let
                                                                                                         ((i.2.sink$2_0 i.1$2_0))
                                                                                                         false)))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              cmp15$1_0
                              (let
                                 ((_$1_5 true))
                                 (=>
                                    (not _$1_5)
                                    (let
                                       ((idxprom27$1_0 i.1$1_0))
                                       (let
                                          ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                          (let
                                             ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                             (let
                                                ((conv29$1_0 _$1_6))
                                                (let
                                                   ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                   (=>
                                                      cmp30$1_0
                                                      (let
                                                         ((retval.0$1_0 0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (hex_digest$2_0 hex_digest$2_0_old)
                                                             (i.1$2_0 i.1$2_0_old))
                                                            (let
                                                               ((s$2_0 s$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (idxprom15$2_0 i.1$2_0))
                                                               (let
                                                                  ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                  (let
                                                                     ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                     (let
                                                                        ((conv17$2_0 _$2_3))
                                                                        (let
                                                                           ((cmp18$2_0 (= conv17$2_0 32)))
                                                                           (=>
                                                                              (not cmp18$2_0)
                                                                              (let
                                                                                 ((idxprom20$2_0 i.1$2_0))
                                                                                 (let
                                                                                    ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                                                                    (let
                                                                                       ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                                                                       (let
                                                                                          ((conv22$2_0 _$2_4))
                                                                                          (let
                                                                                             ((cmp23$2_0 (= conv22$2_0 9)))
                                                                                             (let
                                                                                                ((_$2_5 cmp23$2_0))
                                                                                                (=>
                                                                                                   (not _$2_5)
                                                                                                   (let
                                                                                                      ((idxprom30$2_0 i.1$2_0))
                                                                                                      (let
                                                                                                         ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                                         (let
                                                                                                            ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                                            (let
                                                                                                               ((conv32$2_0 _$2_6))
                                                                                                               (let
                                                                                                                  ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                                  (=>
                                                                                                                     (not cmp33$2_0)
                                                                                                                     (let
                                                                                                                        ((i.2.sink$2_0 i.1$2_0))
                                                                                                                        false))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              (not cmp15$1_0)
                              (let
                                 ((idxprom17$1_0 i.1$1_0))
                                 (let
                                    ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                    (let
                                       ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                       (let
                                          ((conv19$1_0 _$1_4))
                                          (let
                                             ((cmp20$1_0 (= conv19$1_0 9)))
                                             (let
                                                ((_$1_5 cmp20$1_0))
                                                (=>
                                                   (not _$1_5)
                                                   (let
                                                      ((idxprom27$1_0 i.1$1_0))
                                                      (let
                                                         ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                                         (let
                                                            ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                                            (let
                                                               ((conv29$1_0 _$1_6))
                                                               (let
                                                                  ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                                  (=>
                                                                     cmp30$1_0
                                                                     (let
                                                                        ((retval.0$1_0 0))
                                                                        (let
                                                                           ((result$1 retval.0$1_0)
                                                                            (HEAP$1_res HEAP$1)
                                                                            (hex_digest$2_0 hex_digest$2_0_old)
                                                                            (i.1$2_0 i.1$2_0_old))
                                                                           (let
                                                                              ((s$2_0 s$2_0_old)
                                                                               (HEAP$2 HEAP$2_old)
                                                                               (idxprom15$2_0 i.1$2_0))
                                                                              (let
                                                                                 ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                                 (let
                                                                                    ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                                    (let
                                                                                       ((conv17$2_0 _$2_3))
                                                                                       (let
                                                                                          ((cmp18$2_0 (= conv17$2_0 32)))
                                                                                          (=>
                                                                                             cmp18$2_0
                                                                                             (let
                                                                                                ((_$2_5 true))
                                                                                                (=>
                                                                                                   (not _$2_5)
                                                                                                   (let
                                                                                                      ((idxprom30$2_0 i.1$2_0))
                                                                                                      (let
                                                                                                         ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                                         (let
                                                                                                            ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                                            (let
                                                                                                               ((conv32$2_0 _$2_6))
                                                                                                               (let
                                                                                                                  ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                                  (=>
                                                                                                                     (not cmp33$2_0)
                                                                                                                     (let
                                                                                                                        ((i.2.sink$2_0 i.1$2_0))
                                                                                                                        false))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              (not cmp15$1_0)
                              (let
                                 ((idxprom17$1_0 i.1$1_0))
                                 (let
                                    ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                    (let
                                       ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                       (let
                                          ((conv19$1_0 _$1_4))
                                          (let
                                             ((cmp20$1_0 (= conv19$1_0 9)))
                                             (let
                                                ((_$1_5 cmp20$1_0))
                                                (=>
                                                   (not _$1_5)
                                                   (let
                                                      ((idxprom27$1_0 i.1$1_0))
                                                      (let
                                                         ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                                         (let
                                                            ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                                            (let
                                                               ((conv29$1_0 _$1_6))
                                                               (let
                                                                  ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                                  (=>
                                                                     cmp30$1_0
                                                                     (let
                                                                        ((retval.0$1_0 0))
                                                                        (let
                                                                           ((result$1 retval.0$1_0)
                                                                            (HEAP$1_res HEAP$1)
                                                                            (hex_digest$2_0 hex_digest$2_0_old)
                                                                            (i.1$2_0 i.1$2_0_old))
                                                                           (let
                                                                              ((s$2_0 s$2_0_old)
                                                                               (HEAP$2 HEAP$2_old)
                                                                               (idxprom15$2_0 i.1$2_0))
                                                                              (let
                                                                                 ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                                 (let
                                                                                    ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                                    (let
                                                                                       ((conv17$2_0 _$2_3))
                                                                                       (let
                                                                                          ((cmp18$2_0 (= conv17$2_0 32)))
                                                                                          (=>
                                                                                             (not cmp18$2_0)
                                                                                             (let
                                                                                                ((idxprom20$2_0 i.1$2_0))
                                                                                                (let
                                                                                                   ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                                                                                   (let
                                                                                                      ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                                                                                      (let
                                                                                                         ((conv22$2_0 _$2_4))
                                                                                                         (let
                                                                                                            ((cmp23$2_0 (= conv22$2_0 9)))
                                                                                                            (let
                                                                                                               ((_$2_5 cmp23$2_0))
                                                                                                               (=>
                                                                                                                  (not _$2_5)
                                                                                                                  (let
                                                                                                                     ((idxprom30$2_0 i.1$2_0))
                                                                                                                     (let
                                                                                                                        ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                                                        (let
                                                                                                                           ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                                                           (let
                                                                                                                              ((conv32$2_0 _$2_6))
                                                                                                                              (let
                                                                                                                                 ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                                                 (=>
                                                                                                                                    (not cmp33$2_0)
                                                                                                                                    (let
                                                                                                                                       ((i.2.sink$2_0 i.1$2_0))
                                                                                                                                       false)))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              cmp15$1_0
                              (let
                                 ((_$1_5 true))
                                 (=>
                                    (not _$1_5)
                                    (let
                                       ((idxprom27$1_0 i.1$1_0))
                                       (let
                                          ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                          (let
                                             ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                             (let
                                                ((conv29$1_0 _$1_6))
                                                (let
                                                   ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                   (=>
                                                      (not cmp30$1_0)
                                                      (let
                                                         ((i.2.sink$1_0 i.1$1_0)
                                                          (hex_digest$2_0 hex_digest$2_0_old)
                                                          (i.1$2_0 i.1$2_0_old))
                                                         (let
                                                            ((s$2_0 s$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (idxprom15$2_0 i.1$2_0))
                                                            (let
                                                               ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                               (let
                                                                  ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                  (let
                                                                     ((conv17$2_0 _$2_3))
                                                                     (let
                                                                        ((cmp18$2_0 (= conv17$2_0 32)))
                                                                        (=>
                                                                           cmp18$2_0
                                                                           (let
                                                                              ((_$2_5 true))
                                                                              (=>
                                                                                 (not _$2_5)
                                                                                 (let
                                                                                    ((idxprom30$2_0 i.1$2_0))
                                                                                    (let
                                                                                       ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                       (let
                                                                                          ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                          (let
                                                                                             ((conv32$2_0 _$2_6))
                                                                                             (let
                                                                                                ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                (=>
                                                                                                   cmp33$2_0
                                                                                                   (let
                                                                                                      ((retval.0$2_0 0))
                                                                                                      (let
                                                                                                         ((result$2 retval.0$2_0)
                                                                                                          (HEAP$2_res HEAP$2))
                                                                                                         false)))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              cmp15$1_0
                              (let
                                 ((_$1_5 true))
                                 (=>
                                    (not _$1_5)
                                    (let
                                       ((idxprom27$1_0 i.1$1_0))
                                       (let
                                          ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                          (let
                                             ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                             (let
                                                ((conv29$1_0 _$1_6))
                                                (let
                                                   ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                   (=>
                                                      (not cmp30$1_0)
                                                      (let
                                                         ((i.2.sink$1_0 i.1$1_0)
                                                          (hex_digest$2_0 hex_digest$2_0_old)
                                                          (i.1$2_0 i.1$2_0_old))
                                                         (let
                                                            ((s$2_0 s$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (idxprom15$2_0 i.1$2_0))
                                                            (let
                                                               ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                               (let
                                                                  ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                  (let
                                                                     ((conv17$2_0 _$2_3))
                                                                     (let
                                                                        ((cmp18$2_0 (= conv17$2_0 32)))
                                                                        (=>
                                                                           (not cmp18$2_0)
                                                                           (let
                                                                              ((idxprom20$2_0 i.1$2_0))
                                                                              (let
                                                                                 ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                                                                 (let
                                                                                    ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                                                                    (let
                                                                                       ((conv22$2_0 _$2_4))
                                                                                       (let
                                                                                          ((cmp23$2_0 (= conv22$2_0 9)))
                                                                                          (let
                                                                                             ((_$2_5 cmp23$2_0))
                                                                                             (=>
                                                                                                (not _$2_5)
                                                                                                (let
                                                                                                   ((idxprom30$2_0 i.1$2_0))
                                                                                                   (let
                                                                                                      ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                                      (let
                                                                                                         ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                                         (let
                                                                                                            ((conv32$2_0 _$2_6))
                                                                                                            (let
                                                                                                               ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                               (=>
                                                                                                                  cmp33$2_0
                                                                                                                  (let
                                                                                                                     ((retval.0$2_0 0))
                                                                                                                     (let
                                                                                                                        ((result$2 retval.0$2_0)
                                                                                                                         (HEAP$2_res HEAP$2))
                                                                                                                        false))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              (not cmp15$1_0)
                              (let
                                 ((idxprom17$1_0 i.1$1_0))
                                 (let
                                    ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                    (let
                                       ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                       (let
                                          ((conv19$1_0 _$1_4))
                                          (let
                                             ((cmp20$1_0 (= conv19$1_0 9)))
                                             (let
                                                ((_$1_5 cmp20$1_0))
                                                (=>
                                                   (not _$1_5)
                                                   (let
                                                      ((idxprom27$1_0 i.1$1_0))
                                                      (let
                                                         ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                                         (let
                                                            ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                                            (let
                                                               ((conv29$1_0 _$1_6))
                                                               (let
                                                                  ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                                  (=>
                                                                     (not cmp30$1_0)
                                                                     (let
                                                                        ((i.2.sink$1_0 i.1$1_0)
                                                                         (hex_digest$2_0 hex_digest$2_0_old)
                                                                         (i.1$2_0 i.1$2_0_old))
                                                                        (let
                                                                           ((s$2_0 s$2_0_old)
                                                                            (HEAP$2 HEAP$2_old)
                                                                            (idxprom15$2_0 i.1$2_0))
                                                                           (let
                                                                              ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                              (let
                                                                                 ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                                 (let
                                                                                    ((conv17$2_0 _$2_3))
                                                                                    (let
                                                                                       ((cmp18$2_0 (= conv17$2_0 32)))
                                                                                       (=>
                                                                                          cmp18$2_0
                                                                                          (let
                                                                                             ((_$2_5 true))
                                                                                             (=>
                                                                                                (not _$2_5)
                                                                                                (let
                                                                                                   ((idxprom30$2_0 i.1$2_0))
                                                                                                   (let
                                                                                                      ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                                      (let
                                                                                                         ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                                         (let
                                                                                                            ((conv32$2_0 _$2_6))
                                                                                                            (let
                                                                                                               ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                               (=>
                                                                                                                  cmp33$2_0
                                                                                                                  (let
                                                                                                                     ((retval.0$2_0 0))
                                                                                                                     (let
                                                                                                                        ((result$2 retval.0$2_0)
                                                                                                                         (HEAP$2_res HEAP$2))
                                                                                                                        false))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              (not cmp15$1_0)
                              (let
                                 ((idxprom17$1_0 i.1$1_0))
                                 (let
                                    ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                    (let
                                       ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                       (let
                                          ((conv19$1_0 _$1_4))
                                          (let
                                             ((cmp20$1_0 (= conv19$1_0 9)))
                                             (let
                                                ((_$1_5 cmp20$1_0))
                                                (=>
                                                   (not _$1_5)
                                                   (let
                                                      ((idxprom27$1_0 i.1$1_0))
                                                      (let
                                                         ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                                         (let
                                                            ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                                            (let
                                                               ((conv29$1_0 _$1_6))
                                                               (let
                                                                  ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                                  (=>
                                                                     (not cmp30$1_0)
                                                                     (let
                                                                        ((i.2.sink$1_0 i.1$1_0)
                                                                         (hex_digest$2_0 hex_digest$2_0_old)
                                                                         (i.1$2_0 i.1$2_0_old))
                                                                        (let
                                                                           ((s$2_0 s$2_0_old)
                                                                            (HEAP$2 HEAP$2_old)
                                                                            (idxprom15$2_0 i.1$2_0))
                                                                           (let
                                                                              ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                              (let
                                                                                 ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                                 (let
                                                                                    ((conv17$2_0 _$2_3))
                                                                                    (let
                                                                                       ((cmp18$2_0 (= conv17$2_0 32)))
                                                                                       (=>
                                                                                          (not cmp18$2_0)
                                                                                          (let
                                                                                             ((idxprom20$2_0 i.1$2_0))
                                                                                             (let
                                                                                                ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                                                                                (let
                                                                                                   ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                                                                                   (let
                                                                                                      ((conv22$2_0 _$2_4))
                                                                                                      (let
                                                                                                         ((cmp23$2_0 (= conv22$2_0 9)))
                                                                                                         (let
                                                                                                            ((_$2_5 cmp23$2_0))
                                                                                                            (=>
                                                                                                               (not _$2_5)
                                                                                                               (let
                                                                                                                  ((idxprom30$2_0 i.1$2_0))
                                                                                                                  (let
                                                                                                                     ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                                                     (let
                                                                                                                        ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                                                        (let
                                                                                                                           ((conv32$2_0 _$2_6))
                                                                                                                           (let
                                                                                                                              ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                                              (=>
                                                                                                                                 cmp33$2_0
                                                                                                                                 (let
                                                                                                                                    ((retval.0$2_0 0))
                                                                                                                                    (let
                                                                                                                                       ((result$2 retval.0$2_0)
                                                                                                                                        (HEAP$2_res HEAP$2))
                                                                                                                                       false)))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              cmp15$1_0
                              (let
                                 ((_$1_5 true))
                                 (=>
                                    (not _$1_5)
                                    (let
                                       ((idxprom27$1_0 i.1$1_0))
                                       (let
                                          ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                          (let
                                             ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                             (let
                                                ((conv29$1_0 _$1_6))
                                                (let
                                                   ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                   (=>
                                                      cmp30$1_0
                                                      (let
                                                         ((retval.0$1_0 0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (hex_digest$2_0 hex_digest$2_0_old)
                                                             (i.1$2_0 i.1$2_0_old))
                                                            (let
                                                               ((s$2_0 s$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (idxprom15$2_0 i.1$2_0))
                                                               (let
                                                                  ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                  (let
                                                                     ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                     (let
                                                                        ((conv17$2_0 _$2_3))
                                                                        (let
                                                                           ((cmp18$2_0 (= conv17$2_0 32)))
                                                                           (=>
                                                                              cmp18$2_0
                                                                              (let
                                                                                 ((_$2_5 true))
                                                                                 (=>
                                                                                    (not _$2_5)
                                                                                    (let
                                                                                       ((idxprom30$2_0 i.1$2_0))
                                                                                       (let
                                                                                          ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                          (let
                                                                                             ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                             (let
                                                                                                ((conv32$2_0 _$2_6))
                                                                                                (let
                                                                                                   ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                   (=>
                                                                                                      cmp33$2_0
                                                                                                      (let
                                                                                                         ((retval.0$2_0 0))
                                                                                                         (let
                                                                                                            ((result$2 retval.0$2_0)
                                                                                                             (HEAP$2_res HEAP$2))
                                                                                                            (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              cmp15$1_0
                              (let
                                 ((_$1_5 true))
                                 (=>
                                    (not _$1_5)
                                    (let
                                       ((idxprom27$1_0 i.1$1_0))
                                       (let
                                          ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                          (let
                                             ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                             (let
                                                ((conv29$1_0 _$1_6))
                                                (let
                                                   ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                   (=>
                                                      cmp30$1_0
                                                      (let
                                                         ((retval.0$1_0 0))
                                                         (let
                                                            ((result$1 retval.0$1_0)
                                                             (HEAP$1_res HEAP$1)
                                                             (hex_digest$2_0 hex_digest$2_0_old)
                                                             (i.1$2_0 i.1$2_0_old))
                                                            (let
                                                               ((s$2_0 s$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (idxprom15$2_0 i.1$2_0))
                                                               (let
                                                                  ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                  (let
                                                                     ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                     (let
                                                                        ((conv17$2_0 _$2_3))
                                                                        (let
                                                                           ((cmp18$2_0 (= conv17$2_0 32)))
                                                                           (=>
                                                                              (not cmp18$2_0)
                                                                              (let
                                                                                 ((idxprom20$2_0 i.1$2_0))
                                                                                 (let
                                                                                    ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                                                                    (let
                                                                                       ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                                                                       (let
                                                                                          ((conv22$2_0 _$2_4))
                                                                                          (let
                                                                                             ((cmp23$2_0 (= conv22$2_0 9)))
                                                                                             (let
                                                                                                ((_$2_5 cmp23$2_0))
                                                                                                (=>
                                                                                                   (not _$2_5)
                                                                                                   (let
                                                                                                      ((idxprom30$2_0 i.1$2_0))
                                                                                                      (let
                                                                                                         ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                                         (let
                                                                                                            ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                                            (let
                                                                                                               ((conv32$2_0 _$2_6))
                                                                                                               (let
                                                                                                                  ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                                  (=>
                                                                                                                     cmp33$2_0
                                                                                                                     (let
                                                                                                                        ((retval.0$2_0 0))
                                                                                                                        (let
                                                                                                                           ((result$2 retval.0$2_0)
                                                                                                                            (HEAP$2_res HEAP$2))
                                                                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              (not cmp15$1_0)
                              (let
                                 ((idxprom17$1_0 i.1$1_0))
                                 (let
                                    ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                    (let
                                       ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                       (let
                                          ((conv19$1_0 _$1_4))
                                          (let
                                             ((cmp20$1_0 (= conv19$1_0 9)))
                                             (let
                                                ((_$1_5 cmp20$1_0))
                                                (=>
                                                   (not _$1_5)
                                                   (let
                                                      ((idxprom27$1_0 i.1$1_0))
                                                      (let
                                                         ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                                         (let
                                                            ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                                            (let
                                                               ((conv29$1_0 _$1_6))
                                                               (let
                                                                  ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                                  (=>
                                                                     cmp30$1_0
                                                                     (let
                                                                        ((retval.0$1_0 0))
                                                                        (let
                                                                           ((result$1 retval.0$1_0)
                                                                            (HEAP$1_res HEAP$1)
                                                                            (hex_digest$2_0 hex_digest$2_0_old)
                                                                            (i.1$2_0 i.1$2_0_old))
                                                                           (let
                                                                              ((s$2_0 s$2_0_old)
                                                                               (HEAP$2 HEAP$2_old)
                                                                               (idxprom15$2_0 i.1$2_0))
                                                                              (let
                                                                                 ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                                 (let
                                                                                    ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                                    (let
                                                                                       ((conv17$2_0 _$2_3))
                                                                                       (let
                                                                                          ((cmp18$2_0 (= conv17$2_0 32)))
                                                                                          (=>
                                                                                             cmp18$2_0
                                                                                             (let
                                                                                                ((_$2_5 true))
                                                                                                (=>
                                                                                                   (not _$2_5)
                                                                                                   (let
                                                                                                      ((idxprom30$2_0 i.1$2_0))
                                                                                                      (let
                                                                                                         ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                                         (let
                                                                                                            ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                                            (let
                                                                                                               ((conv32$2_0 _$2_6))
                                                                                                               (let
                                                                                                                  ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                                  (=>
                                                                                                                     cmp33$2_0
                                                                                                                     (let
                                                                                                                        ((retval.0$2_0 0))
                                                                                                                        (let
                                                                                                                           ((result$2 retval.0$2_0)
                                                                                                                            (HEAP$2_res HEAP$2))
                                                                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              (not cmp15$1_0)
                              (let
                                 ((idxprom17$1_0 i.1$1_0))
                                 (let
                                    ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                    (let
                                       ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                       (let
                                          ((conv19$1_0 _$1_4))
                                          (let
                                             ((cmp20$1_0 (= conv19$1_0 9)))
                                             (let
                                                ((_$1_5 cmp20$1_0))
                                                (=>
                                                   (not _$1_5)
                                                   (let
                                                      ((idxprom27$1_0 i.1$1_0))
                                                      (let
                                                         ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                                         (let
                                                            ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                                            (let
                                                               ((conv29$1_0 _$1_6))
                                                               (let
                                                                  ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                                  (=>
                                                                     cmp30$1_0
                                                                     (let
                                                                        ((retval.0$1_0 0))
                                                                        (let
                                                                           ((result$1 retval.0$1_0)
                                                                            (HEAP$1_res HEAP$1)
                                                                            (hex_digest$2_0 hex_digest$2_0_old)
                                                                            (i.1$2_0 i.1$2_0_old))
                                                                           (let
                                                                              ((s$2_0 s$2_0_old)
                                                                               (HEAP$2 HEAP$2_old)
                                                                               (idxprom15$2_0 i.1$2_0))
                                                                              (let
                                                                                 ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                                 (let
                                                                                    ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                                    (let
                                                                                       ((conv17$2_0 _$2_3))
                                                                                       (let
                                                                                          ((cmp18$2_0 (= conv17$2_0 32)))
                                                                                          (=>
                                                                                             (not cmp18$2_0)
                                                                                             (let
                                                                                                ((idxprom20$2_0 i.1$2_0))
                                                                                                (let
                                                                                                   ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                                                                                   (let
                                                                                                      ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                                                                                      (let
                                                                                                         ((conv22$2_0 _$2_4))
                                                                                                         (let
                                                                                                            ((cmp23$2_0 (= conv22$2_0 9)))
                                                                                                            (let
                                                                                                               ((_$2_5 cmp23$2_0))
                                                                                                               (=>
                                                                                                                  (not _$2_5)
                                                                                                                  (let
                                                                                                                     ((idxprom30$2_0 i.1$2_0))
                                                                                                                     (let
                                                                                                                        ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                                                        (let
                                                                                                                           ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                                                           (let
                                                                                                                              ((conv32$2_0 _$2_6))
                                                                                                                              (let
                                                                                                                                 ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                                                 (=>
                                                                                                                                    cmp33$2_0
                                                                                                                                    (let
                                                                                                                                       ((retval.0$2_0 0))
                                                                                                                                       (let
                                                                                                                                          ((result$2 retval.0$2_0)
                                                                                                                                           (HEAP$2_res HEAP$2))
                                                                                                                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              cmp15$1_0
                              (let
                                 ((_$1_5 true))
                                 (=>
                                    _$1_5
                                    (let
                                       ((inc25$1_0 (+ i.1$1_0 1)))
                                       (let
                                          ((i.1$1_0 inc25$1_0)
                                           (hex_digest$2_0 hex_digest$2_0_old)
                                           (i.1$2_0 i.1$2_0_old))
                                          (let
                                             ((s$2_0 s$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (idxprom15$2_0 i.1$2_0))
                                             (let
                                                ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                (let
                                                   ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                   (let
                                                      ((conv17$2_0 _$2_3))
                                                      (let
                                                         ((cmp18$2_0 (= conv17$2_0 32)))
                                                         (=>
                                                            cmp18$2_0
                                                            (let
                                                               ((_$2_5 true))
                                                               (=>
                                                                  _$2_5
                                                                  (let
                                                                     ((inc28$2_0 (+ i.1$2_0 1)))
                                                                     (let
                                                                        ((i.1$2_0 inc28$2_0))
                                                                        (forall
                                                                           ((i1 Int)
                                                                            (i2 Int))
                                                                           (INV_MAIN_2 hex_digest$1_0 i.1$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.1$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              cmp15$1_0
                              (let
                                 ((_$1_5 true))
                                 (=>
                                    _$1_5
                                    (let
                                       ((inc25$1_0 (+ i.1$1_0 1)))
                                       (let
                                          ((i.1$1_0 inc25$1_0)
                                           (hex_digest$2_0 hex_digest$2_0_old)
                                           (i.1$2_0 i.1$2_0_old))
                                          (let
                                             ((s$2_0 s$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (idxprom15$2_0 i.1$2_0))
                                             (let
                                                ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                (let
                                                   ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                   (let
                                                      ((conv17$2_0 _$2_3))
                                                      (let
                                                         ((cmp18$2_0 (= conv17$2_0 32)))
                                                         (=>
                                                            (not cmp18$2_0)
                                                            (let
                                                               ((idxprom20$2_0 i.1$2_0))
                                                               (let
                                                                  ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                                                  (let
                                                                     ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                                                     (let
                                                                        ((conv22$2_0 _$2_4))
                                                                        (let
                                                                           ((cmp23$2_0 (= conv22$2_0 9)))
                                                                           (let
                                                                              ((_$2_5 cmp23$2_0))
                                                                              (=>
                                                                                 _$2_5
                                                                                 (let
                                                                                    ((inc28$2_0 (+ i.1$2_0 1)))
                                                                                    (let
                                                                                       ((i.1$2_0 inc28$2_0))
                                                                                       (forall
                                                                                          ((i1 Int)
                                                                                           (i2 Int))
                                                                                          (INV_MAIN_2 hex_digest$1_0 i.1$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.1$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              (not cmp15$1_0)
                              (let
                                 ((idxprom17$1_0 i.1$1_0))
                                 (let
                                    ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                    (let
                                       ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                       (let
                                          ((conv19$1_0 _$1_4))
                                          (let
                                             ((cmp20$1_0 (= conv19$1_0 9)))
                                             (let
                                                ((_$1_5 cmp20$1_0))
                                                (=>
                                                   _$1_5
                                                   (let
                                                      ((inc25$1_0 (+ i.1$1_0 1)))
                                                      (let
                                                         ((i.1$1_0 inc25$1_0)
                                                          (hex_digest$2_0 hex_digest$2_0_old)
                                                          (i.1$2_0 i.1$2_0_old))
                                                         (let
                                                            ((s$2_0 s$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (idxprom15$2_0 i.1$2_0))
                                                            (let
                                                               ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                               (let
                                                                  ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                  (let
                                                                     ((conv17$2_0 _$2_3))
                                                                     (let
                                                                        ((cmp18$2_0 (= conv17$2_0 32)))
                                                                        (=>
                                                                           cmp18$2_0
                                                                           (let
                                                                              ((_$2_5 true))
                                                                              (=>
                                                                                 _$2_5
                                                                                 (let
                                                                                    ((inc28$2_0 (+ i.1$2_0 1)))
                                                                                    (let
                                                                                       ((i.1$2_0 inc28$2_0))
                                                                                       (forall
                                                                                          ((i1 Int)
                                                                                           (i2 Int))
                                                                                          (INV_MAIN_2 hex_digest$1_0 i.1$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.1$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              (not cmp15$1_0)
                              (let
                                 ((idxprom17$1_0 i.1$1_0))
                                 (let
                                    ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                    (let
                                       ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                       (let
                                          ((conv19$1_0 _$1_4))
                                          (let
                                             ((cmp20$1_0 (= conv19$1_0 9)))
                                             (let
                                                ((_$1_5 cmp20$1_0))
                                                (=>
                                                   _$1_5
                                                   (let
                                                      ((inc25$1_0 (+ i.1$1_0 1)))
                                                      (let
                                                         ((i.1$1_0 inc25$1_0)
                                                          (hex_digest$2_0 hex_digest$2_0_old)
                                                          (i.1$2_0 i.1$2_0_old))
                                                         (let
                                                            ((s$2_0 s$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (idxprom15$2_0 i.1$2_0))
                                                            (let
                                                               ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                               (let
                                                                  ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                  (let
                                                                     ((conv17$2_0 _$2_3))
                                                                     (let
                                                                        ((cmp18$2_0 (= conv17$2_0 32)))
                                                                        (=>
                                                                           (not cmp18$2_0)
                                                                           (let
                                                                              ((idxprom20$2_0 i.1$2_0))
                                                                              (let
                                                                                 ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                                                                 (let
                                                                                    ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                                                                    (let
                                                                                       ((conv22$2_0 _$2_4))
                                                                                       (let
                                                                                          ((cmp23$2_0 (= conv22$2_0 9)))
                                                                                          (let
                                                                                             ((_$2_5 cmp23$2_0))
                                                                                             (=>
                                                                                                _$2_5
                                                                                                (let
                                                                                                   ((inc28$2_0 (+ i.1$2_0 1)))
                                                                                                   (let
                                                                                                      ((i.1$2_0 inc28$2_0))
                                                                                                      (forall
                                                                                                         ((i1 Int)
                                                                                                          (i2 Int))
                                                                                                         (INV_MAIN_2 hex_digest$1_0 i.1$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.1$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              cmp15$1_0
                              (let
                                 ((_$1_5 true))
                                 (=>
                                    _$1_5
                                    (let
                                       ((inc25$1_0 (+ i.1$1_0 1)))
                                       (let
                                          ((i.1$1_0 inc25$1_0))
                                          (=>
                                             (and
                                                (let
                                                   ((hex_digest$2_0 hex_digest$2_0_old)
                                                    (i.1$2_0 i.1$2_0_old))
                                                   (let
                                                      ((s$2_0 s$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (idxprom15$2_0 i.1$2_0))
                                                      (let
                                                         ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                         (let
                                                            ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                            (let
                                                               ((conv17$2_0 _$2_3))
                                                               (let
                                                                  ((cmp18$2_0 (= conv17$2_0 32)))
                                                                  (=>
                                                                     cmp18$2_0
                                                                     (let
                                                                        ((_$2_5 true))
                                                                        (=>
                                                                           _$2_5
                                                                           (let
                                                                              ((inc28$2_0 (+ i.1$2_0 1)))
                                                                              (let
                                                                                 ((i.1$2_0 inc28$2_0))
                                                                                 false)))))))))))
                                                (let
                                                   ((hex_digest$2_0 hex_digest$2_0_old)
                                                    (i.1$2_0 i.1$2_0_old))
                                                   (let
                                                      ((s$2_0 s$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (idxprom15$2_0 i.1$2_0))
                                                      (let
                                                         ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                         (let
                                                            ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                            (let
                                                               ((conv17$2_0 _$2_3))
                                                               (let
                                                                  ((cmp18$2_0 (= conv17$2_0 32)))
                                                                  (=>
                                                                     (not cmp18$2_0)
                                                                     (let
                                                                        ((idxprom20$2_0 i.1$2_0))
                                                                        (let
                                                                           ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                                                           (let
                                                                              ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                                                              (let
                                                                                 ((conv22$2_0 _$2_4))
                                                                                 (let
                                                                                    ((cmp23$2_0 (= conv22$2_0 9)))
                                                                                    (let
                                                                                       ((_$2_5 cmp23$2_0))
                                                                                       (=>
                                                                                          _$2_5
                                                                                          (let
                                                                                             ((inc28$2_0 (+ i.1$2_0 1)))
                                                                                             (let
                                                                                                ((i.1$2_0 inc28$2_0))
                                                                                                false)))))))))))))))))
                                             (forall
                                                ((i1 Int)
                                                 (i2_old Int))
                                                (INV_MAIN_2 hex_digest$1_0 i.1$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              (not cmp15$1_0)
                              (let
                                 ((idxprom17$1_0 i.1$1_0))
                                 (let
                                    ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                    (let
                                       ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                       (let
                                          ((conv19$1_0 _$1_4))
                                          (let
                                             ((cmp20$1_0 (= conv19$1_0 9)))
                                             (let
                                                ((_$1_5 cmp20$1_0))
                                                (=>
                                                   _$1_5
                                                   (let
                                                      ((inc25$1_0 (+ i.1$1_0 1)))
                                                      (let
                                                         ((i.1$1_0 inc25$1_0))
                                                         (=>
                                                            (and
                                                               (let
                                                                  ((hex_digest$2_0 hex_digest$2_0_old)
                                                                   (i.1$2_0 i.1$2_0_old))
                                                                  (let
                                                                     ((s$2_0 s$2_0_old)
                                                                      (HEAP$2 HEAP$2_old)
                                                                      (idxprom15$2_0 i.1$2_0))
                                                                     (let
                                                                        ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                        (let
                                                                           ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                           (let
                                                                              ((conv17$2_0 _$2_3))
                                                                              (let
                                                                                 ((cmp18$2_0 (= conv17$2_0 32)))
                                                                                 (=>
                                                                                    cmp18$2_0
                                                                                    (let
                                                                                       ((_$2_5 true))
                                                                                       (=>
                                                                                          _$2_5
                                                                                          (let
                                                                                             ((inc28$2_0 (+ i.1$2_0 1)))
                                                                                             (let
                                                                                                ((i.1$2_0 inc28$2_0))
                                                                                                false)))))))))))
                                                               (let
                                                                  ((hex_digest$2_0 hex_digest$2_0_old)
                                                                   (i.1$2_0 i.1$2_0_old))
                                                                  (let
                                                                     ((s$2_0 s$2_0_old)
                                                                      (HEAP$2 HEAP$2_old)
                                                                      (idxprom15$2_0 i.1$2_0))
                                                                     (let
                                                                        ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                        (let
                                                                           ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                           (let
                                                                              ((conv17$2_0 _$2_3))
                                                                              (let
                                                                                 ((cmp18$2_0 (= conv17$2_0 32)))
                                                                                 (=>
                                                                                    (not cmp18$2_0)
                                                                                    (let
                                                                                       ((idxprom20$2_0 i.1$2_0))
                                                                                       (let
                                                                                          ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                                                                          (let
                                                                                             ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                                                                             (let
                                                                                                ((conv22$2_0 _$2_4))
                                                                                                (let
                                                                                                   ((cmp23$2_0 (= conv22$2_0 9)))
                                                                                                   (let
                                                                                                      ((_$2_5 cmp23$2_0))
                                                                                                      (=>
                                                                                                         _$2_5
                                                                                                         (let
                                                                                                            ((inc28$2_0 (+ i.1$2_0 1)))
                                                                                                            (let
                                                                                                               ((i.1$2_0 inc28$2_0))
                                                                                                               false)))))))))))))))))
                                                            (forall
                                                               ((i1 Int)
                                                                (i2_old Int))
                                                               (INV_MAIN_2 hex_digest$1_0 i.1$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$2_0 hex_digest$2_0_old)
             (i.1$2_0 i.1$2_0_old))
            (let
               ((s$2_0 s$2_0_old)
                (HEAP$2 HEAP$2_old)
                (idxprom15$2_0 i.1$2_0))
               (let
                  ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                  (let
                     ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                     (let
                        ((conv17$2_0 _$2_3))
                        (let
                           ((cmp18$2_0 (= conv17$2_0 32)))
                           (=>
                              cmp18$2_0
                              (let
                                 ((_$2_5 true))
                                 (=>
                                    _$2_5
                                    (let
                                       ((inc28$2_0 (+ i.1$2_0 1)))
                                       (let
                                          ((i.1$2_0 inc28$2_0))
                                          (=>
                                             (and
                                                (let
                                                   ((hex_digest$1_0 hex_digest$1_0_old)
                                                    (i.1$1_0 i.1$1_0_old))
                                                   (let
                                                      ((s$1_0 s$1_0_old)
                                                       (HEAP$1 HEAP$1_old)
                                                       (idxprom12$1_0 i.1$1_0))
                                                      (let
                                                         ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                                                         (let
                                                            ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                                                            (let
                                                               ((conv14$1_0 _$1_3))
                                                               (let
                                                                  ((cmp15$1_0 (= conv14$1_0 32)))
                                                                  (=>
                                                                     cmp15$1_0
                                                                     (let
                                                                        ((_$1_5 true))
                                                                        (=>
                                                                           _$1_5
                                                                           (let
                                                                              ((inc25$1_0 (+ i.1$1_0 1)))
                                                                              (let
                                                                                 ((i.1$1_0 inc25$1_0))
                                                                                 false)))))))))))
                                                (let
                                                   ((hex_digest$1_0 hex_digest$1_0_old)
                                                    (i.1$1_0 i.1$1_0_old))
                                                   (let
                                                      ((s$1_0 s$1_0_old)
                                                       (HEAP$1 HEAP$1_old)
                                                       (idxprom12$1_0 i.1$1_0))
                                                      (let
                                                         ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                                                         (let
                                                            ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                                                            (let
                                                               ((conv14$1_0 _$1_3))
                                                               (let
                                                                  ((cmp15$1_0 (= conv14$1_0 32)))
                                                                  (=>
                                                                     (not cmp15$1_0)
                                                                     (let
                                                                        ((idxprom17$1_0 i.1$1_0))
                                                                        (let
                                                                           ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                                                           (let
                                                                              ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                                                              (let
                                                                                 ((conv19$1_0 _$1_4))
                                                                                 (let
                                                                                    ((cmp20$1_0 (= conv19$1_0 9)))
                                                                                    (let
                                                                                       ((_$1_5 cmp20$1_0))
                                                                                       (=>
                                                                                          _$1_5
                                                                                          (let
                                                                                             ((inc25$1_0 (+ i.1$1_0 1)))
                                                                                             (let
                                                                                                ((i.1$1_0 inc25$1_0))
                                                                                                false)))))))))))))))))
                                             (forall
                                                ((i1_old Int)
                                                 (i2 Int))
                                                (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0 i.1$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$2_0 hex_digest$2_0_old)
             (i.1$2_0 i.1$2_0_old))
            (let
               ((s$2_0 s$2_0_old)
                (HEAP$2 HEAP$2_old)
                (idxprom15$2_0 i.1$2_0))
               (let
                  ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                  (let
                     ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                     (let
                        ((conv17$2_0 _$2_3))
                        (let
                           ((cmp18$2_0 (= conv17$2_0 32)))
                           (=>
                              (not cmp18$2_0)
                              (let
                                 ((idxprom20$2_0 i.1$2_0))
                                 (let
                                    ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                    (let
                                       ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                       (let
                                          ((conv22$2_0 _$2_4))
                                          (let
                                             ((cmp23$2_0 (= conv22$2_0 9)))
                                             (let
                                                ((_$2_5 cmp23$2_0))
                                                (=>
                                                   _$2_5
                                                   (let
                                                      ((inc28$2_0 (+ i.1$2_0 1)))
                                                      (let
                                                         ((i.1$2_0 inc28$2_0))
                                                         (=>
                                                            (and
                                                               (let
                                                                  ((hex_digest$1_0 hex_digest$1_0_old)
                                                                   (i.1$1_0 i.1$1_0_old))
                                                                  (let
                                                                     ((s$1_0 s$1_0_old)
                                                                      (HEAP$1 HEAP$1_old)
                                                                      (idxprom12$1_0 i.1$1_0))
                                                                     (let
                                                                        ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                                                                        (let
                                                                           ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                                                                           (let
                                                                              ((conv14$1_0 _$1_3))
                                                                              (let
                                                                                 ((cmp15$1_0 (= conv14$1_0 32)))
                                                                                 (=>
                                                                                    cmp15$1_0
                                                                                    (let
                                                                                       ((_$1_5 true))
                                                                                       (=>
                                                                                          _$1_5
                                                                                          (let
                                                                                             ((inc25$1_0 (+ i.1$1_0 1)))
                                                                                             (let
                                                                                                ((i.1$1_0 inc25$1_0))
                                                                                                false)))))))))))
                                                               (let
                                                                  ((hex_digest$1_0 hex_digest$1_0_old)
                                                                   (i.1$1_0 i.1$1_0_old))
                                                                  (let
                                                                     ((s$1_0 s$1_0_old)
                                                                      (HEAP$1 HEAP$1_old)
                                                                      (idxprom12$1_0 i.1$1_0))
                                                                     (let
                                                                        ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                                                                        (let
                                                                           ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                                                                           (let
                                                                              ((conv14$1_0 _$1_3))
                                                                              (let
                                                                                 ((cmp15$1_0 (= conv14$1_0 32)))
                                                                                 (=>
                                                                                    (not cmp15$1_0)
                                                                                    (let
                                                                                       ((idxprom17$1_0 i.1$1_0))
                                                                                       (let
                                                                                          ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                                                                          (let
                                                                                             ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                                                                             (let
                                                                                                ((conv19$1_0 _$1_4))
                                                                                                (let
                                                                                                   ((cmp20$1_0 (= conv19$1_0 9)))
                                                                                                   (let
                                                                                                      ((_$1_5 cmp20$1_0))
                                                                                                      (=>
                                                                                                         _$1_5
                                                                                                         (let
                                                                                                            ((inc25$1_0 (+ i.1$1_0 1)))
                                                                                                            (let
                                                                                                               ((i.1$1_0 inc25$1_0))
                                                                                                               false)))))))))))))))))
                                                            (forall
                                                               ((i1_old Int)
                                                                (i2 Int))
                                                               (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0 i.1$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              cmp15$1_0
                              (let
                                 ((_$1_5 true))
                                 (=>
                                    (not _$1_5)
                                    (let
                                       ((idxprom27$1_0 i.1$1_0))
                                       (let
                                          ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                          (let
                                             ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                             (let
                                                ((conv29$1_0 _$1_6))
                                                (let
                                                   ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                   (=>
                                                      (not cmp30$1_0)
                                                      (let
                                                         ((i.2.sink$1_0 i.1$1_0)
                                                          (hex_digest$2_0 hex_digest$2_0_old)
                                                          (i.1$2_0 i.1$2_0_old))
                                                         (let
                                                            ((s$2_0 s$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (idxprom15$2_0 i.1$2_0))
                                                            (let
                                                               ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                               (let
                                                                  ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                  (let
                                                                     ((conv17$2_0 _$2_3))
                                                                     (let
                                                                        ((cmp18$2_0 (= conv17$2_0 32)))
                                                                        (=>
                                                                           cmp18$2_0
                                                                           (let
                                                                              ((_$2_5 true))
                                                                              (=>
                                                                                 (not _$2_5)
                                                                                 (let
                                                                                    ((idxprom30$2_0 i.1$2_0))
                                                                                    (let
                                                                                       ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                       (let
                                                                                          ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                          (let
                                                                                             ((conv32$2_0 _$2_6))
                                                                                             (let
                                                                                                ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                (=>
                                                                                                   (not cmp33$2_0)
                                                                                                   (let
                                                                                                      ((i.2.sink$2_0 i.1$2_0))
                                                                                                      (forall
                                                                                                         ((i1 Int)
                                                                                                          (i2 Int))
                                                                                                         (INV_MAIN_3 hex_digest$1_0 i.2.sink$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.2.sink$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              cmp15$1_0
                              (let
                                 ((_$1_5 true))
                                 (=>
                                    (not _$1_5)
                                    (let
                                       ((idxprom27$1_0 i.1$1_0))
                                       (let
                                          ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                          (let
                                             ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                             (let
                                                ((conv29$1_0 _$1_6))
                                                (let
                                                   ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                   (=>
                                                      (not cmp30$1_0)
                                                      (let
                                                         ((i.2.sink$1_0 i.1$1_0)
                                                          (hex_digest$2_0 hex_digest$2_0_old)
                                                          (i.1$2_0 i.1$2_0_old))
                                                         (let
                                                            ((s$2_0 s$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (idxprom15$2_0 i.1$2_0))
                                                            (let
                                                               ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                               (let
                                                                  ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                  (let
                                                                     ((conv17$2_0 _$2_3))
                                                                     (let
                                                                        ((cmp18$2_0 (= conv17$2_0 32)))
                                                                        (=>
                                                                           (not cmp18$2_0)
                                                                           (let
                                                                              ((idxprom20$2_0 i.1$2_0))
                                                                              (let
                                                                                 ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                                                                 (let
                                                                                    ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                                                                    (let
                                                                                       ((conv22$2_0 _$2_4))
                                                                                       (let
                                                                                          ((cmp23$2_0 (= conv22$2_0 9)))
                                                                                          (let
                                                                                             ((_$2_5 cmp23$2_0))
                                                                                             (=>
                                                                                                (not _$2_5)
                                                                                                (let
                                                                                                   ((idxprom30$2_0 i.1$2_0))
                                                                                                   (let
                                                                                                      ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                                      (let
                                                                                                         ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                                         (let
                                                                                                            ((conv32$2_0 _$2_6))
                                                                                                            (let
                                                                                                               ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                               (=>
                                                                                                                  (not cmp33$2_0)
                                                                                                                  (let
                                                                                                                     ((i.2.sink$2_0 i.1$2_0))
                                                                                                                     (forall
                                                                                                                        ((i1 Int)
                                                                                                                         (i2 Int))
                                                                                                                        (INV_MAIN_3 hex_digest$1_0 i.2.sink$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.2.sink$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              (not cmp15$1_0)
                              (let
                                 ((idxprom17$1_0 i.1$1_0))
                                 (let
                                    ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                    (let
                                       ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                       (let
                                          ((conv19$1_0 _$1_4))
                                          (let
                                             ((cmp20$1_0 (= conv19$1_0 9)))
                                             (let
                                                ((_$1_5 cmp20$1_0))
                                                (=>
                                                   (not _$1_5)
                                                   (let
                                                      ((idxprom27$1_0 i.1$1_0))
                                                      (let
                                                         ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                                         (let
                                                            ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                                            (let
                                                               ((conv29$1_0 _$1_6))
                                                               (let
                                                                  ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                                  (=>
                                                                     (not cmp30$1_0)
                                                                     (let
                                                                        ((i.2.sink$1_0 i.1$1_0)
                                                                         (hex_digest$2_0 hex_digest$2_0_old)
                                                                         (i.1$2_0 i.1$2_0_old))
                                                                        (let
                                                                           ((s$2_0 s$2_0_old)
                                                                            (HEAP$2 HEAP$2_old)
                                                                            (idxprom15$2_0 i.1$2_0))
                                                                           (let
                                                                              ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                              (let
                                                                                 ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                                 (let
                                                                                    ((conv17$2_0 _$2_3))
                                                                                    (let
                                                                                       ((cmp18$2_0 (= conv17$2_0 32)))
                                                                                       (=>
                                                                                          cmp18$2_0
                                                                                          (let
                                                                                             ((_$2_5 true))
                                                                                             (=>
                                                                                                (not _$2_5)
                                                                                                (let
                                                                                                   ((idxprom30$2_0 i.1$2_0))
                                                                                                   (let
                                                                                                      ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                                      (let
                                                                                                         ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                                         (let
                                                                                                            ((conv32$2_0 _$2_6))
                                                                                                            (let
                                                                                                               ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                               (=>
                                                                                                                  (not cmp33$2_0)
                                                                                                                  (let
                                                                                                                     ((i.2.sink$2_0 i.1$2_0))
                                                                                                                     (forall
                                                                                                                        ((i1 Int)
                                                                                                                         (i2 Int))
                                                                                                                        (INV_MAIN_3 hex_digest$1_0 i.2.sink$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.2.sink$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.1$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.1$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_2 hex_digest$1_0_old i.1$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.1$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.1$1_0 i.1$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (idxprom12$1_0 i.1$1_0))
               (let
                  ((arrayidx13$1_0 (+ s$1_0 idxprom12$1_0)))
                  (let
                     ((_$1_3 (select HEAP$1 arrayidx13$1_0)))
                     (let
                        ((conv14$1_0 _$1_3))
                        (let
                           ((cmp15$1_0 (= conv14$1_0 32)))
                           (=>
                              (not cmp15$1_0)
                              (let
                                 ((idxprom17$1_0 i.1$1_0))
                                 (let
                                    ((arrayidx18$1_0 (+ s$1_0 idxprom17$1_0)))
                                    (let
                                       ((_$1_4 (select HEAP$1 arrayidx18$1_0)))
                                       (let
                                          ((conv19$1_0 _$1_4))
                                          (let
                                             ((cmp20$1_0 (= conv19$1_0 9)))
                                             (let
                                                ((_$1_5 cmp20$1_0))
                                                (=>
                                                   (not _$1_5)
                                                   (let
                                                      ((idxprom27$1_0 i.1$1_0))
                                                      (let
                                                         ((arrayidx28$1_0 (+ s$1_0 idxprom27$1_0)))
                                                         (let
                                                            ((_$1_6 (select HEAP$1 arrayidx28$1_0)))
                                                            (let
                                                               ((conv29$1_0 _$1_6))
                                                               (let
                                                                  ((cmp30$1_0 (distinct conv29$1_0 61)))
                                                                  (=>
                                                                     (not cmp30$1_0)
                                                                     (let
                                                                        ((i.2.sink$1_0 i.1$1_0)
                                                                         (hex_digest$2_0 hex_digest$2_0_old)
                                                                         (i.1$2_0 i.1$2_0_old))
                                                                        (let
                                                                           ((s$2_0 s$2_0_old)
                                                                            (HEAP$2 HEAP$2_old)
                                                                            (idxprom15$2_0 i.1$2_0))
                                                                           (let
                                                                              ((arrayidx16$2_0 (+ s$2_0 idxprom15$2_0)))
                                                                              (let
                                                                                 ((_$2_3 (select HEAP$2 arrayidx16$2_0)))
                                                                                 (let
                                                                                    ((conv17$2_0 _$2_3))
                                                                                    (let
                                                                                       ((cmp18$2_0 (= conv17$2_0 32)))
                                                                                       (=>
                                                                                          (not cmp18$2_0)
                                                                                          (let
                                                                                             ((idxprom20$2_0 i.1$2_0))
                                                                                             (let
                                                                                                ((arrayidx21$2_0 (+ s$2_0 idxprom20$2_0)))
                                                                                                (let
                                                                                                   ((_$2_4 (select HEAP$2 arrayidx21$2_0)))
                                                                                                   (let
                                                                                                      ((conv22$2_0 _$2_4))
                                                                                                      (let
                                                                                                         ((cmp23$2_0 (= conv22$2_0 9)))
                                                                                                         (let
                                                                                                            ((_$2_5 cmp23$2_0))
                                                                                                            (=>
                                                                                                               (not _$2_5)
                                                                                                               (let
                                                                                                                  ((idxprom30$2_0 i.1$2_0))
                                                                                                                  (let
                                                                                                                     ((arrayidx31$2_0 (+ s$2_0 idxprom30$2_0)))
                                                                                                                     (let
                                                                                                                        ((_$2_6 (select HEAP$2 arrayidx31$2_0)))
                                                                                                                        (let
                                                                                                                           ((conv32$2_0 _$2_6))
                                                                                                                           (let
                                                                                                                              ((cmp33$2_0 (distinct conv32$2_0 61)))
                                                                                                                              (=>
                                                                                                                                 (not cmp33$2_0)
                                                                                                                                 (let
                                                                                                                                    ((i.2.sink$2_0 i.1$2_0))
                                                                                                                                    (forall
                                                                                                                                       ((i1 Int)
                                                                                                                                        (i2 Int))
                                                                                                                                       (INV_MAIN_3 hex_digest$1_0 i.2.sink$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.2.sink$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.2.sink$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.2.sink$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.2.sink$1_0 i.2.sink$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc53$1_0 (+ i.2.sink$1_0 1)))
               (let
                  ((idxprom37$1_0 inc53$1_0))
                  (let
                     ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                     (let
                        ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                        (let
                           ((conv39$1_0 _$1_7))
                           (let
                              ((cmp40$1_0 (= conv39$1_0 32)))
                              (=>
                                 cmp40$1_0
                                 (let
                                    ((_$1_9 true))
                                    (=>
                                       (not _$1_9)
                                       (let
                                          ((idxprom55$1_0 inc53$1_0))
                                          (let
                                             ((arrayidx56$1_0 (+ s$1_0 idxprom55$1_0)))
                                             (let
                                                ((HEAP$1 (store HEAP$1 hex_digest$1_0 arrayidx56$1_0))
                                                 (retval.0$1_0 1))
                                                (let
                                                   ((result$1 retval.0$1_0)
                                                    (HEAP$1_res HEAP$1)
                                                    (hex_digest$2_0 hex_digest$2_0_old)
                                                    (i.2.sink$2_0 i.2.sink$2_0_old))
                                                   (let
                                                      ((s$2_0 s$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (inc56$2_0 (+ i.2.sink$2_0 1)))
                                                      (let
                                                         ((idxprom40$2_0 inc56$2_0))
                                                         (let
                                                            ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                                                            (let
                                                               ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                                                               (let
                                                                  ((conv42$2_0 _$2_7))
                                                                  (let
                                                                     ((cmp43$2_0 (= conv42$2_0 32)))
                                                                     (=>
                                                                        cmp43$2_0
                                                                        (let
                                                                           ((_$2_9 true))
                                                                           (=>
                                                                              (not _$2_9)
                                                                              (let
                                                                                 ((idxprom58$2_0 inc56$2_0))
                                                                                 (let
                                                                                    ((arrayidx59$2_0 (+ s$2_0 idxprom58$2_0)))
                                                                                    (let
                                                                                       ((HEAP$2 (store HEAP$2 hex_digest$2_0 arrayidx59$2_0))
                                                                                        (retval.0$2_0 1))
                                                                                       (let
                                                                                          ((result$2 retval.0$2_0)
                                                                                           (HEAP$2_res HEAP$2))
                                                                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.2.sink$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.2.sink$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.2.sink$1_0 i.2.sink$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc53$1_0 (+ i.2.sink$1_0 1)))
               (let
                  ((idxprom37$1_0 inc53$1_0))
                  (let
                     ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                     (let
                        ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                        (let
                           ((conv39$1_0 _$1_7))
                           (let
                              ((cmp40$1_0 (= conv39$1_0 32)))
                              (=>
                                 cmp40$1_0
                                 (let
                                    ((_$1_9 true))
                                    (=>
                                       (not _$1_9)
                                       (let
                                          ((idxprom55$1_0 inc53$1_0))
                                          (let
                                             ((arrayidx56$1_0 (+ s$1_0 idxprom55$1_0)))
                                             (let
                                                ((HEAP$1 (store HEAP$1 hex_digest$1_0 arrayidx56$1_0))
                                                 (retval.0$1_0 1))
                                                (let
                                                   ((result$1 retval.0$1_0)
                                                    (HEAP$1_res HEAP$1)
                                                    (hex_digest$2_0 hex_digest$2_0_old)
                                                    (i.2.sink$2_0 i.2.sink$2_0_old))
                                                   (let
                                                      ((s$2_0 s$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (inc56$2_0 (+ i.2.sink$2_0 1)))
                                                      (let
                                                         ((idxprom40$2_0 inc56$2_0))
                                                         (let
                                                            ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                                                            (let
                                                               ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                                                               (let
                                                                  ((conv42$2_0 _$2_7))
                                                                  (let
                                                                     ((cmp43$2_0 (= conv42$2_0 32)))
                                                                     (=>
                                                                        (not cmp43$2_0)
                                                                        (let
                                                                           ((idxprom46$2_0 inc56$2_0))
                                                                           (let
                                                                              ((arrayidx47$2_0 (+ s$2_0 idxprom46$2_0)))
                                                                              (let
                                                                                 ((_$2_8 (select HEAP$2 arrayidx47$2_0)))
                                                                                 (let
                                                                                    ((conv48$2_0 _$2_8))
                                                                                    (let
                                                                                       ((cmp49$2_0 (= conv48$2_0 9)))
                                                                                       (let
                                                                                          ((_$2_9 cmp49$2_0))
                                                                                          (=>
                                                                                             (not _$2_9)
                                                                                             (let
                                                                                                ((idxprom58$2_0 inc56$2_0))
                                                                                                (let
                                                                                                   ((arrayidx59$2_0 (+ s$2_0 idxprom58$2_0)))
                                                                                                   (let
                                                                                                      ((HEAP$2 (store HEAP$2 hex_digest$2_0 arrayidx59$2_0))
                                                                                                       (retval.0$2_0 1))
                                                                                                      (let
                                                                                                         ((result$2 retval.0$2_0)
                                                                                                          (HEAP$2_res HEAP$2))
                                                                                                         (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.2.sink$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.2.sink$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.2.sink$1_0 i.2.sink$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc53$1_0 (+ i.2.sink$1_0 1)))
               (let
                  ((idxprom37$1_0 inc53$1_0))
                  (let
                     ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                     (let
                        ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                        (let
                           ((conv39$1_0 _$1_7))
                           (let
                              ((cmp40$1_0 (= conv39$1_0 32)))
                              (=>
                                 (not cmp40$1_0)
                                 (let
                                    ((idxprom43$1_0 inc53$1_0))
                                    (let
                                       ((arrayidx44$1_0 (+ s$1_0 idxprom43$1_0)))
                                       (let
                                          ((_$1_8 (select HEAP$1 arrayidx44$1_0)))
                                          (let
                                             ((conv45$1_0 _$1_8))
                                             (let
                                                ((cmp46$1_0 (= conv45$1_0 9)))
                                                (let
                                                   ((_$1_9 cmp46$1_0))
                                                   (=>
                                                      (not _$1_9)
                                                      (let
                                                         ((idxprom55$1_0 inc53$1_0))
                                                         (let
                                                            ((arrayidx56$1_0 (+ s$1_0 idxprom55$1_0)))
                                                            (let
                                                               ((HEAP$1 (store HEAP$1 hex_digest$1_0 arrayidx56$1_0))
                                                                (retval.0$1_0 1))
                                                               (let
                                                                  ((result$1 retval.0$1_0)
                                                                   (HEAP$1_res HEAP$1)
                                                                   (hex_digest$2_0 hex_digest$2_0_old)
                                                                   (i.2.sink$2_0 i.2.sink$2_0_old))
                                                                  (let
                                                                     ((s$2_0 s$2_0_old)
                                                                      (HEAP$2 HEAP$2_old)
                                                                      (inc56$2_0 (+ i.2.sink$2_0 1)))
                                                                     (let
                                                                        ((idxprom40$2_0 inc56$2_0))
                                                                        (let
                                                                           ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                                                                           (let
                                                                              ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                                                                              (let
                                                                                 ((conv42$2_0 _$2_7))
                                                                                 (let
                                                                                    ((cmp43$2_0 (= conv42$2_0 32)))
                                                                                    (=>
                                                                                       cmp43$2_0
                                                                                       (let
                                                                                          ((_$2_9 true))
                                                                                          (=>
                                                                                             (not _$2_9)
                                                                                             (let
                                                                                                ((idxprom58$2_0 inc56$2_0))
                                                                                                (let
                                                                                                   ((arrayidx59$2_0 (+ s$2_0 idxprom58$2_0)))
                                                                                                   (let
                                                                                                      ((HEAP$2 (store HEAP$2 hex_digest$2_0 arrayidx59$2_0))
                                                                                                       (retval.0$2_0 1))
                                                                                                      (let
                                                                                                         ((result$2 retval.0$2_0)
                                                                                                          (HEAP$2_res HEAP$2))
                                                                                                         (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.2.sink$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.2.sink$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.2.sink$1_0 i.2.sink$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc53$1_0 (+ i.2.sink$1_0 1)))
               (let
                  ((idxprom37$1_0 inc53$1_0))
                  (let
                     ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                     (let
                        ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                        (let
                           ((conv39$1_0 _$1_7))
                           (let
                              ((cmp40$1_0 (= conv39$1_0 32)))
                              (=>
                                 (not cmp40$1_0)
                                 (let
                                    ((idxprom43$1_0 inc53$1_0))
                                    (let
                                       ((arrayidx44$1_0 (+ s$1_0 idxprom43$1_0)))
                                       (let
                                          ((_$1_8 (select HEAP$1 arrayidx44$1_0)))
                                          (let
                                             ((conv45$1_0 _$1_8))
                                             (let
                                                ((cmp46$1_0 (= conv45$1_0 9)))
                                                (let
                                                   ((_$1_9 cmp46$1_0))
                                                   (=>
                                                      (not _$1_9)
                                                      (let
                                                         ((idxprom55$1_0 inc53$1_0))
                                                         (let
                                                            ((arrayidx56$1_0 (+ s$1_0 idxprom55$1_0)))
                                                            (let
                                                               ((HEAP$1 (store HEAP$1 hex_digest$1_0 arrayidx56$1_0))
                                                                (retval.0$1_0 1))
                                                               (let
                                                                  ((result$1 retval.0$1_0)
                                                                   (HEAP$1_res HEAP$1)
                                                                   (hex_digest$2_0 hex_digest$2_0_old)
                                                                   (i.2.sink$2_0 i.2.sink$2_0_old))
                                                                  (let
                                                                     ((s$2_0 s$2_0_old)
                                                                      (HEAP$2 HEAP$2_old)
                                                                      (inc56$2_0 (+ i.2.sink$2_0 1)))
                                                                     (let
                                                                        ((idxprom40$2_0 inc56$2_0))
                                                                        (let
                                                                           ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                                                                           (let
                                                                              ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                                                                              (let
                                                                                 ((conv42$2_0 _$2_7))
                                                                                 (let
                                                                                    ((cmp43$2_0 (= conv42$2_0 32)))
                                                                                    (=>
                                                                                       (not cmp43$2_0)
                                                                                       (let
                                                                                          ((idxprom46$2_0 inc56$2_0))
                                                                                          (let
                                                                                             ((arrayidx47$2_0 (+ s$2_0 idxprom46$2_0)))
                                                                                             (let
                                                                                                ((_$2_8 (select HEAP$2 arrayidx47$2_0)))
                                                                                                (let
                                                                                                   ((conv48$2_0 _$2_8))
                                                                                                   (let
                                                                                                      ((cmp49$2_0 (= conv48$2_0 9)))
                                                                                                      (let
                                                                                                         ((_$2_9 cmp49$2_0))
                                                                                                         (=>
                                                                                                            (not _$2_9)
                                                                                                            (let
                                                                                                               ((idxprom58$2_0 inc56$2_0))
                                                                                                               (let
                                                                                                                  ((arrayidx59$2_0 (+ s$2_0 idxprom58$2_0)))
                                                                                                                  (let
                                                                                                                     ((HEAP$2 (store HEAP$2 hex_digest$2_0 arrayidx59$2_0))
                                                                                                                      (retval.0$2_0 1))
                                                                                                                     (let
                                                                                                                        ((result$2 retval.0$2_0)
                                                                                                                         (HEAP$2_res HEAP$2))
                                                                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.2.sink$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.2.sink$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.2.sink$1_0 i.2.sink$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc53$1_0 (+ i.2.sink$1_0 1)))
               (let
                  ((idxprom37$1_0 inc53$1_0))
                  (let
                     ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                     (let
                        ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                        (let
                           ((conv39$1_0 _$1_7))
                           (let
                              ((cmp40$1_0 (= conv39$1_0 32)))
                              (=>
                                 cmp40$1_0
                                 (let
                                    ((_$1_9 true))
                                    (=>
                                       _$1_9
                                       (let
                                          ((i.2.sink$1_0 inc53$1_0)
                                           (hex_digest$2_0 hex_digest$2_0_old)
                                           (i.2.sink$2_0 i.2.sink$2_0_old))
                                          (let
                                             ((s$2_0 s$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (inc56$2_0 (+ i.2.sink$2_0 1)))
                                             (let
                                                ((idxprom40$2_0 inc56$2_0))
                                                (let
                                                   ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                                                   (let
                                                      ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                                                      (let
                                                         ((conv42$2_0 _$2_7))
                                                         (let
                                                            ((cmp43$2_0 (= conv42$2_0 32)))
                                                            (=>
                                                               cmp43$2_0
                                                               (let
                                                                  ((_$2_9 true))
                                                                  (=>
                                                                     _$2_9
                                                                     (let
                                                                        ((i.2.sink$2_0 inc56$2_0))
                                                                        (forall
                                                                           ((i1 Int)
                                                                            (i2 Int))
                                                                           (INV_MAIN_3 hex_digest$1_0 i.2.sink$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.2.sink$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.2.sink$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.2.sink$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.2.sink$1_0 i.2.sink$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc53$1_0 (+ i.2.sink$1_0 1)))
               (let
                  ((idxprom37$1_0 inc53$1_0))
                  (let
                     ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                     (let
                        ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                        (let
                           ((conv39$1_0 _$1_7))
                           (let
                              ((cmp40$1_0 (= conv39$1_0 32)))
                              (=>
                                 cmp40$1_0
                                 (let
                                    ((_$1_9 true))
                                    (=>
                                       _$1_9
                                       (let
                                          ((i.2.sink$1_0 inc53$1_0)
                                           (hex_digest$2_0 hex_digest$2_0_old)
                                           (i.2.sink$2_0 i.2.sink$2_0_old))
                                          (let
                                             ((s$2_0 s$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (inc56$2_0 (+ i.2.sink$2_0 1)))
                                             (let
                                                ((idxprom40$2_0 inc56$2_0))
                                                (let
                                                   ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                                                   (let
                                                      ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                                                      (let
                                                         ((conv42$2_0 _$2_7))
                                                         (let
                                                            ((cmp43$2_0 (= conv42$2_0 32)))
                                                            (=>
                                                               (not cmp43$2_0)
                                                               (let
                                                                  ((idxprom46$2_0 inc56$2_0))
                                                                  (let
                                                                     ((arrayidx47$2_0 (+ s$2_0 idxprom46$2_0)))
                                                                     (let
                                                                        ((_$2_8 (select HEAP$2 arrayidx47$2_0)))
                                                                        (let
                                                                           ((conv48$2_0 _$2_8))
                                                                           (let
                                                                              ((cmp49$2_0 (= conv48$2_0 9)))
                                                                              (let
                                                                                 ((_$2_9 cmp49$2_0))
                                                                                 (=>
                                                                                    _$2_9
                                                                                    (let
                                                                                       ((i.2.sink$2_0 inc56$2_0))
                                                                                       (forall
                                                                                          ((i1 Int)
                                                                                           (i2 Int))
                                                                                          (INV_MAIN_3 hex_digest$1_0 i.2.sink$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.2.sink$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.2.sink$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.2.sink$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.2.sink$1_0 i.2.sink$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc53$1_0 (+ i.2.sink$1_0 1)))
               (let
                  ((idxprom37$1_0 inc53$1_0))
                  (let
                     ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                     (let
                        ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                        (let
                           ((conv39$1_0 _$1_7))
                           (let
                              ((cmp40$1_0 (= conv39$1_0 32)))
                              (=>
                                 (not cmp40$1_0)
                                 (let
                                    ((idxprom43$1_0 inc53$1_0))
                                    (let
                                       ((arrayidx44$1_0 (+ s$1_0 idxprom43$1_0)))
                                       (let
                                          ((_$1_8 (select HEAP$1 arrayidx44$1_0)))
                                          (let
                                             ((conv45$1_0 _$1_8))
                                             (let
                                                ((cmp46$1_0 (= conv45$1_0 9)))
                                                (let
                                                   ((_$1_9 cmp46$1_0))
                                                   (=>
                                                      _$1_9
                                                      (let
                                                         ((i.2.sink$1_0 inc53$1_0)
                                                          (hex_digest$2_0 hex_digest$2_0_old)
                                                          (i.2.sink$2_0 i.2.sink$2_0_old))
                                                         (let
                                                            ((s$2_0 s$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (inc56$2_0 (+ i.2.sink$2_0 1)))
                                                            (let
                                                               ((idxprom40$2_0 inc56$2_0))
                                                               (let
                                                                  ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                                                                  (let
                                                                     ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                                                                     (let
                                                                        ((conv42$2_0 _$2_7))
                                                                        (let
                                                                           ((cmp43$2_0 (= conv42$2_0 32)))
                                                                           (=>
                                                                              cmp43$2_0
                                                                              (let
                                                                                 ((_$2_9 true))
                                                                                 (=>
                                                                                    _$2_9
                                                                                    (let
                                                                                       ((i.2.sink$2_0 inc56$2_0))
                                                                                       (forall
                                                                                          ((i1 Int)
                                                                                           (i2 Int))
                                                                                          (INV_MAIN_3 hex_digest$1_0 i.2.sink$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.2.sink$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.2.sink$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.2.sink$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.2.sink$1_0 i.2.sink$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc53$1_0 (+ i.2.sink$1_0 1)))
               (let
                  ((idxprom37$1_0 inc53$1_0))
                  (let
                     ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                     (let
                        ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                        (let
                           ((conv39$1_0 _$1_7))
                           (let
                              ((cmp40$1_0 (= conv39$1_0 32)))
                              (=>
                                 (not cmp40$1_0)
                                 (let
                                    ((idxprom43$1_0 inc53$1_0))
                                    (let
                                       ((arrayidx44$1_0 (+ s$1_0 idxprom43$1_0)))
                                       (let
                                          ((_$1_8 (select HEAP$1 arrayidx44$1_0)))
                                          (let
                                             ((conv45$1_0 _$1_8))
                                             (let
                                                ((cmp46$1_0 (= conv45$1_0 9)))
                                                (let
                                                   ((_$1_9 cmp46$1_0))
                                                   (=>
                                                      _$1_9
                                                      (let
                                                         ((i.2.sink$1_0 inc53$1_0)
                                                          (hex_digest$2_0 hex_digest$2_0_old)
                                                          (i.2.sink$2_0 i.2.sink$2_0_old))
                                                         (let
                                                            ((s$2_0 s$2_0_old)
                                                             (HEAP$2 HEAP$2_old)
                                                             (inc56$2_0 (+ i.2.sink$2_0 1)))
                                                            (let
                                                               ((idxprom40$2_0 inc56$2_0))
                                                               (let
                                                                  ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                                                                  (let
                                                                     ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                                                                     (let
                                                                        ((conv42$2_0 _$2_7))
                                                                        (let
                                                                           ((cmp43$2_0 (= conv42$2_0 32)))
                                                                           (=>
                                                                              (not cmp43$2_0)
                                                                              (let
                                                                                 ((idxprom46$2_0 inc56$2_0))
                                                                                 (let
                                                                                    ((arrayidx47$2_0 (+ s$2_0 idxprom46$2_0)))
                                                                                    (let
                                                                                       ((_$2_8 (select HEAP$2 arrayidx47$2_0)))
                                                                                       (let
                                                                                          ((conv48$2_0 _$2_8))
                                                                                          (let
                                                                                             ((cmp49$2_0 (= conv48$2_0 9)))
                                                                                             (let
                                                                                                ((_$2_9 cmp49$2_0))
                                                                                                (=>
                                                                                                   _$2_9
                                                                                                   (let
                                                                                                      ((i.2.sink$2_0 inc56$2_0))
                                                                                                      (forall
                                                                                                         ((i1 Int)
                                                                                                          (i2 Int))
                                                                                                         (INV_MAIN_3 hex_digest$1_0 i.2.sink$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0 i.2.sink$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.2.sink$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.2.sink$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.2.sink$1_0 i.2.sink$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc53$1_0 (+ i.2.sink$1_0 1)))
               (let
                  ((idxprom37$1_0 inc53$1_0))
                  (let
                     ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                     (let
                        ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                        (let
                           ((conv39$1_0 _$1_7))
                           (let
                              ((cmp40$1_0 (= conv39$1_0 32)))
                              (=>
                                 cmp40$1_0
                                 (let
                                    ((_$1_9 true))
                                    (=>
                                       _$1_9
                                       (let
                                          ((i.2.sink$1_0 inc53$1_0))
                                          (=>
                                             (and
                                                (let
                                                   ((hex_digest$2_0 hex_digest$2_0_old)
                                                    (i.2.sink$2_0 i.2.sink$2_0_old))
                                                   (let
                                                      ((s$2_0 s$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (inc56$2_0 (+ i.2.sink$2_0 1)))
                                                      (let
                                                         ((idxprom40$2_0 inc56$2_0))
                                                         (let
                                                            ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                                                            (let
                                                               ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                                                               (let
                                                                  ((conv42$2_0 _$2_7))
                                                                  (let
                                                                     ((cmp43$2_0 (= conv42$2_0 32)))
                                                                     (=>
                                                                        cmp43$2_0
                                                                        (let
                                                                           ((_$2_9 true))
                                                                           (=>
                                                                              _$2_9
                                                                              (let
                                                                                 ((i.2.sink$2_0 inc56$2_0))
                                                                                 false)))))))))))
                                                (let
                                                   ((hex_digest$2_0 hex_digest$2_0_old)
                                                    (i.2.sink$2_0 i.2.sink$2_0_old))
                                                   (let
                                                      ((s$2_0 s$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (inc56$2_0 (+ i.2.sink$2_0 1)))
                                                      (let
                                                         ((idxprom40$2_0 inc56$2_0))
                                                         (let
                                                            ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                                                            (let
                                                               ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                                                               (let
                                                                  ((conv42$2_0 _$2_7))
                                                                  (let
                                                                     ((cmp43$2_0 (= conv42$2_0 32)))
                                                                     (=>
                                                                        (not cmp43$2_0)
                                                                        (let
                                                                           ((idxprom46$2_0 inc56$2_0))
                                                                           (let
                                                                              ((arrayidx47$2_0 (+ s$2_0 idxprom46$2_0)))
                                                                              (let
                                                                                 ((_$2_8 (select HEAP$2 arrayidx47$2_0)))
                                                                                 (let
                                                                                    ((conv48$2_0 _$2_8))
                                                                                    (let
                                                                                       ((cmp49$2_0 (= conv48$2_0 9)))
                                                                                       (let
                                                                                          ((_$2_9 cmp49$2_0))
                                                                                          (=>
                                                                                             _$2_9
                                                                                             (let
                                                                                                ((i.2.sink$2_0 inc56$2_0))
                                                                                                false)))))))))))))))))
                                             (forall
                                                ((i1 Int)
                                                 (i2_old Int))
                                                (INV_MAIN_3 hex_digest$1_0 i.2.sink$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.2.sink$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.2.sink$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$1_0 hex_digest$1_0_old)
             (i.2.sink$1_0 i.2.sink$1_0_old))
            (let
               ((s$1_0 s$1_0_old)
                (HEAP$1 HEAP$1_old)
                (inc53$1_0 (+ i.2.sink$1_0 1)))
               (let
                  ((idxprom37$1_0 inc53$1_0))
                  (let
                     ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                     (let
                        ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                        (let
                           ((conv39$1_0 _$1_7))
                           (let
                              ((cmp40$1_0 (= conv39$1_0 32)))
                              (=>
                                 (not cmp40$1_0)
                                 (let
                                    ((idxprom43$1_0 inc53$1_0))
                                    (let
                                       ((arrayidx44$1_0 (+ s$1_0 idxprom43$1_0)))
                                       (let
                                          ((_$1_8 (select HEAP$1 arrayidx44$1_0)))
                                          (let
                                             ((conv45$1_0 _$1_8))
                                             (let
                                                ((cmp46$1_0 (= conv45$1_0 9)))
                                                (let
                                                   ((_$1_9 cmp46$1_0))
                                                   (=>
                                                      _$1_9
                                                      (let
                                                         ((i.2.sink$1_0 inc53$1_0))
                                                         (=>
                                                            (and
                                                               (let
                                                                  ((hex_digest$2_0 hex_digest$2_0_old)
                                                                   (i.2.sink$2_0 i.2.sink$2_0_old))
                                                                  (let
                                                                     ((s$2_0 s$2_0_old)
                                                                      (HEAP$2 HEAP$2_old)
                                                                      (inc56$2_0 (+ i.2.sink$2_0 1)))
                                                                     (let
                                                                        ((idxprom40$2_0 inc56$2_0))
                                                                        (let
                                                                           ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                                                                           (let
                                                                              ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                                                                              (let
                                                                                 ((conv42$2_0 _$2_7))
                                                                                 (let
                                                                                    ((cmp43$2_0 (= conv42$2_0 32)))
                                                                                    (=>
                                                                                       cmp43$2_0
                                                                                       (let
                                                                                          ((_$2_9 true))
                                                                                          (=>
                                                                                             _$2_9
                                                                                             (let
                                                                                                ((i.2.sink$2_0 inc56$2_0))
                                                                                                false)))))))))))
                                                               (let
                                                                  ((hex_digest$2_0 hex_digest$2_0_old)
                                                                   (i.2.sink$2_0 i.2.sink$2_0_old))
                                                                  (let
                                                                     ((s$2_0 s$2_0_old)
                                                                      (HEAP$2 HEAP$2_old)
                                                                      (inc56$2_0 (+ i.2.sink$2_0 1)))
                                                                     (let
                                                                        ((idxprom40$2_0 inc56$2_0))
                                                                        (let
                                                                           ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                                                                           (let
                                                                              ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                                                                              (let
                                                                                 ((conv42$2_0 _$2_7))
                                                                                 (let
                                                                                    ((cmp43$2_0 (= conv42$2_0 32)))
                                                                                    (=>
                                                                                       (not cmp43$2_0)
                                                                                       (let
                                                                                          ((idxprom46$2_0 inc56$2_0))
                                                                                          (let
                                                                                             ((arrayidx47$2_0 (+ s$2_0 idxprom46$2_0)))
                                                                                             (let
                                                                                                ((_$2_8 (select HEAP$2 arrayidx47$2_0)))
                                                                                                (let
                                                                                                   ((conv48$2_0 _$2_8))
                                                                                                   (let
                                                                                                      ((cmp49$2_0 (= conv48$2_0 9)))
                                                                                                      (let
                                                                                                         ((_$2_9 cmp49$2_0))
                                                                                                         (=>
                                                                                                            _$2_9
                                                                                                            (let
                                                                                                               ((i.2.sink$2_0 inc56$2_0))
                                                                                                               false)))))))))))))))))
                                                            (forall
                                                               ((i1 Int)
                                                                (i2_old Int))
                                                               (INV_MAIN_3 hex_digest$1_0 i.2.sink$1_0 s$1_0 i1 (select HEAP$1 i1) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.2.sink$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.2.sink$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$2_0 hex_digest$2_0_old)
             (i.2.sink$2_0 i.2.sink$2_0_old))
            (let
               ((s$2_0 s$2_0_old)
                (HEAP$2 HEAP$2_old)
                (inc56$2_0 (+ i.2.sink$2_0 1)))
               (let
                  ((idxprom40$2_0 inc56$2_0))
                  (let
                     ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                     (let
                        ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                        (let
                           ((conv42$2_0 _$2_7))
                           (let
                              ((cmp43$2_0 (= conv42$2_0 32)))
                              (=>
                                 cmp43$2_0
                                 (let
                                    ((_$2_9 true))
                                    (=>
                                       _$2_9
                                       (let
                                          ((i.2.sink$2_0 inc56$2_0))
                                          (=>
                                             (and
                                                (let
                                                   ((hex_digest$1_0 hex_digest$1_0_old)
                                                    (i.2.sink$1_0 i.2.sink$1_0_old))
                                                   (let
                                                      ((s$1_0 s$1_0_old)
                                                       (HEAP$1 HEAP$1_old)
                                                       (inc53$1_0 (+ i.2.sink$1_0 1)))
                                                      (let
                                                         ((idxprom37$1_0 inc53$1_0))
                                                         (let
                                                            ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                                                            (let
                                                               ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                                                               (let
                                                                  ((conv39$1_0 _$1_7))
                                                                  (let
                                                                     ((cmp40$1_0 (= conv39$1_0 32)))
                                                                     (=>
                                                                        cmp40$1_0
                                                                        (let
                                                                           ((_$1_9 true))
                                                                           (=>
                                                                              _$1_9
                                                                              (let
                                                                                 ((i.2.sink$1_0 inc53$1_0))
                                                                                 false)))))))))))
                                                (let
                                                   ((hex_digest$1_0 hex_digest$1_0_old)
                                                    (i.2.sink$1_0 i.2.sink$1_0_old))
                                                   (let
                                                      ((s$1_0 s$1_0_old)
                                                       (HEAP$1 HEAP$1_old)
                                                       (inc53$1_0 (+ i.2.sink$1_0 1)))
                                                      (let
                                                         ((idxprom37$1_0 inc53$1_0))
                                                         (let
                                                            ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                                                            (let
                                                               ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                                                               (let
                                                                  ((conv39$1_0 _$1_7))
                                                                  (let
                                                                     ((cmp40$1_0 (= conv39$1_0 32)))
                                                                     (=>
                                                                        (not cmp40$1_0)
                                                                        (let
                                                                           ((idxprom43$1_0 inc53$1_0))
                                                                           (let
                                                                              ((arrayidx44$1_0 (+ s$1_0 idxprom43$1_0)))
                                                                              (let
                                                                                 ((_$1_8 (select HEAP$1 arrayidx44$1_0)))
                                                                                 (let
                                                                                    ((conv45$1_0 _$1_8))
                                                                                    (let
                                                                                       ((cmp46$1_0 (= conv45$1_0 9)))
                                                                                       (let
                                                                                          ((_$1_9 cmp46$1_0))
                                                                                          (=>
                                                                                             _$1_9
                                                                                             (let
                                                                                                ((i.2.sink$1_0 inc53$1_0))
                                                                                                false)))))))))))))))))
                                             (forall
                                                ((i1_old Int)
                                                 (i2 Int))
                                                (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0 i.2.sink$2_0 s$2_0 i2 (select HEAP$2 i2))))))))))))))))))
(assert
   (forall
      ((hex_digest$1_0_old Int)
       (i.2.sink$1_0_old Int)
       (s$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (hex_digest$2_0_old Int)
       (i.2.sink$2_0_old Int)
       (s$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0_old i.2.sink$2_0_old s$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((hex_digest$2_0 hex_digest$2_0_old)
             (i.2.sink$2_0 i.2.sink$2_0_old))
            (let
               ((s$2_0 s$2_0_old)
                (HEAP$2 HEAP$2_old)
                (inc56$2_0 (+ i.2.sink$2_0 1)))
               (let
                  ((idxprom40$2_0 inc56$2_0))
                  (let
                     ((arrayidx41$2_0 (+ s$2_0 idxprom40$2_0)))
                     (let
                        ((_$2_7 (select HEAP$2 arrayidx41$2_0)))
                        (let
                           ((conv42$2_0 _$2_7))
                           (let
                              ((cmp43$2_0 (= conv42$2_0 32)))
                              (=>
                                 (not cmp43$2_0)
                                 (let
                                    ((idxprom46$2_0 inc56$2_0))
                                    (let
                                       ((arrayidx47$2_0 (+ s$2_0 idxprom46$2_0)))
                                       (let
                                          ((_$2_8 (select HEAP$2 arrayidx47$2_0)))
                                          (let
                                             ((conv48$2_0 _$2_8))
                                             (let
                                                ((cmp49$2_0 (= conv48$2_0 9)))
                                                (let
                                                   ((_$2_9 cmp49$2_0))
                                                   (=>
                                                      _$2_9
                                                      (let
                                                         ((i.2.sink$2_0 inc56$2_0))
                                                         (=>
                                                            (and
                                                               (let
                                                                  ((hex_digest$1_0 hex_digest$1_0_old)
                                                                   (i.2.sink$1_0 i.2.sink$1_0_old))
                                                                  (let
                                                                     ((s$1_0 s$1_0_old)
                                                                      (HEAP$1 HEAP$1_old)
                                                                      (inc53$1_0 (+ i.2.sink$1_0 1)))
                                                                     (let
                                                                        ((idxprom37$1_0 inc53$1_0))
                                                                        (let
                                                                           ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                                                                           (let
                                                                              ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                                                                              (let
                                                                                 ((conv39$1_0 _$1_7))
                                                                                 (let
                                                                                    ((cmp40$1_0 (= conv39$1_0 32)))
                                                                                    (=>
                                                                                       cmp40$1_0
                                                                                       (let
                                                                                          ((_$1_9 true))
                                                                                          (=>
                                                                                             _$1_9
                                                                                             (let
                                                                                                ((i.2.sink$1_0 inc53$1_0))
                                                                                                false)))))))))))
                                                               (let
                                                                  ((hex_digest$1_0 hex_digest$1_0_old)
                                                                   (i.2.sink$1_0 i.2.sink$1_0_old))
                                                                  (let
                                                                     ((s$1_0 s$1_0_old)
                                                                      (HEAP$1 HEAP$1_old)
                                                                      (inc53$1_0 (+ i.2.sink$1_0 1)))
                                                                     (let
                                                                        ((idxprom37$1_0 inc53$1_0))
                                                                        (let
                                                                           ((arrayidx38$1_0 (+ s$1_0 idxprom37$1_0)))
                                                                           (let
                                                                              ((_$1_7 (select HEAP$1 arrayidx38$1_0)))
                                                                              (let
                                                                                 ((conv39$1_0 _$1_7))
                                                                                 (let
                                                                                    ((cmp40$1_0 (= conv39$1_0 32)))
                                                                                    (=>
                                                                                       (not cmp40$1_0)
                                                                                       (let
                                                                                          ((idxprom43$1_0 inc53$1_0))
                                                                                          (let
                                                                                             ((arrayidx44$1_0 (+ s$1_0 idxprom43$1_0)))
                                                                                             (let
                                                                                                ((_$1_8 (select HEAP$1 arrayidx44$1_0)))
                                                                                                (let
                                                                                                   ((conv45$1_0 _$1_8))
                                                                                                   (let
                                                                                                      ((cmp46$1_0 (= conv45$1_0 9)))
                                                                                                      (let
                                                                                                         ((_$1_9 cmp46$1_0))
                                                                                                         (=>
                                                                                                            _$1_9
                                                                                                            (let
                                                                                                               ((i.2.sink$1_0 inc53$1_0))
                                                                                                               false)))))))))))))))))
                                                            (forall
                                                               ((i1_old Int)
                                                                (i2 Int))
                                                               (INV_MAIN_3 hex_digest$1_0_old i.2.sink$1_0_old s$1_0_old i1_old (select HEAP$1_old i1_old) hex_digest$2_0 i.2.sink$2_0 s$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))
(check-sat)
(get-model)
