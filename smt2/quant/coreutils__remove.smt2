;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((fd$1_0 Int)
    (file$1_0 Int)
    (st_size$1_0 Int)
    (st_ino$1_0 Int)
    (flag$1_0 Int)
    (errno$1_0 Int)
    (fstatat$1_0 Int)
    (HEAP$1 (Array Int Int))
    (fd$2_0 Int)
    (file$2_0 Int)
    (st_size$2_0 Int)
    (st_ino$2_0 Int)
    (flag$2_0 Int)
    (errno$2_0 Int)
    (fstatat$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= fd$1_0 fd$2_0)
      (= file$1_0 file$2_0)
      (= st_size$1_0 st_size$2_0)
      (= st_ino$1_0 st_ino$2_0)
      (= flag$1_0 flag$2_0)
      (= errno$1_0 errno$2_0)
      (= fstatat$1_0 fstatat$2_0)
      (forall
         ((i_0 Int))
         (= (select HEAP$1 i_0) (select HEAP$2 i_0)))
      (>= file$1_0 0)
      (>= errno$1_0 0)
      (>= fstatat$1_0 0)
      (>= file$2_0 0)
      (>= errno$2_0 0)
      (>= fstatat$2_0 0)
      (distinct st_size$1_0 (- 1))
      (= st_ino$2_0 (- (- 1) st_size$1_0))))
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
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           cmp1$1_0
                           (let
                              ((_$1_1 (select HEAP$1 errno$1_0)))
                              (let
                                 ((sub$1_0 (- (- 1) _$1_1)))
                                 (let
                                    ((st_size.addr.0$1_0 sub$1_0))
                                    (let
                                       ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                       (=>
                                          cmp2$1_0
                                          (let
                                             ((retval.0$1_0 0))
                                             (let
                                                ((result$1 retval.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (fd$2_0 fd$2_0_old)
                                                 (file$2_0 file$2_0_old)
                                                 (st_size$2_0 st_size$2_0_old))
                                                (let
                                                   ((st_ino$2_0 st_ino$2_0_old)
                                                    (flag$2_0 flag$2_0_old)
                                                    (errno$2_0 errno$2_0_old)
                                                    (fstatat$2_0 fstatat$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (cmp$2_0 (= st_size$2_0 (- 1))))
                                                   (=>
                                                      cmp$2_0
                                                      (let
                                                         ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                         (let
                                                            ((cmp1$2_0 (distinct _$2_0 0)))
                                                            (=>
                                                               cmp1$2_0
                                                               (let
                                                                  ((_$2_1 (select HEAP$2 errno$2_0))
                                                                   (st_size.addr.0$2_0 (- 2)))
                                                                  (let
                                                                     ((st_ino.addr.0$2_0 _$2_1)
                                                                      (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                                     (=>
                                                                        cmp2$2_0
                                                                        (let
                                                                           ((retval.0$2_0 0))
                                                                           (let
                                                                              ((result$2 retval.0$2_0)
                                                                               (HEAP$2_res HEAP$2))
                                                                              (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           cmp1$1_0
                           (let
                              ((_$1_1 (select HEAP$1 errno$1_0)))
                              (let
                                 ((sub$1_0 (- (- 1) _$1_1)))
                                 (let
                                    ((st_size.addr.0$1_0 sub$1_0))
                                    (let
                                       ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                       (=>
                                          cmp2$1_0
                                          (let
                                             ((retval.0$1_0 0))
                                             (let
                                                ((result$1 retval.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (fd$2_0 fd$2_0_old)
                                                 (file$2_0 file$2_0_old)
                                                 (st_size$2_0 st_size$2_0_old))
                                                (let
                                                   ((st_ino$2_0 st_ino$2_0_old)
                                                    (flag$2_0 flag$2_0_old)
                                                    (errno$2_0 errno$2_0_old)
                                                    (fstatat$2_0 fstatat$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (cmp$2_0 (= st_size$2_0 (- 1))))
                                                   (=>
                                                      cmp$2_0
                                                      (let
                                                         ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                         (let
                                                            ((cmp1$2_0 (distinct _$2_0 0)))
                                                            (=>
                                                               cmp1$2_0
                                                               (let
                                                                  ((_$2_1 (select HEAP$2 errno$2_0))
                                                                   (st_size.addr.0$2_0 (- 2)))
                                                                  (let
                                                                     ((st_ino.addr.0$2_0 _$2_1)
                                                                      (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                                     (=>
                                                                        (not cmp2$2_0)
                                                                        (let
                                                                           ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                            (retval.0$2_0 (- 1)))
                                                                           (let
                                                                              ((result$2 retval.0$2_0)
                                                                               (HEAP$2_res HEAP$2))
                                                                              (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           cmp1$1_0
                           (let
                              ((_$1_1 (select HEAP$1 errno$1_0)))
                              (let
                                 ((sub$1_0 (- (- 1) _$1_1)))
                                 (let
                                    ((st_size.addr.0$1_0 sub$1_0))
                                    (let
                                       ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                       (=>
                                          cmp2$1_0
                                          (let
                                             ((retval.0$1_0 0))
                                             (let
                                                ((result$1 retval.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (fd$2_0 fd$2_0_old)
                                                 (file$2_0 file$2_0_old)
                                                 (st_size$2_0 st_size$2_0_old))
                                                (let
                                                   ((st_ino$2_0 st_ino$2_0_old)
                                                    (flag$2_0 flag$2_0_old)
                                                    (errno$2_0 errno$2_0_old)
                                                    (fstatat$2_0 fstatat$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (cmp$2_0 (= st_size$2_0 (- 1))))
                                                   (=>
                                                      cmp$2_0
                                                      (let
                                                         ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                         (let
                                                            ((cmp1$2_0 (distinct _$2_0 0)))
                                                            (=>
                                                               (not cmp1$2_0)
                                                               (let
                                                                  ((st_size.addr.0$2_0 st_size$2_0))
                                                                  (let
                                                                     ((st_ino.addr.0$2_0 st_ino$2_0)
                                                                      (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                                     (=>
                                                                        cmp2$2_0
                                                                        (let
                                                                           ((retval.0$2_0 0))
                                                                           (let
                                                                              ((result$2 retval.0$2_0)
                                                                               (HEAP$2_res HEAP$2))
                                                                              (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           cmp1$1_0
                           (let
                              ((_$1_1 (select HEAP$1 errno$1_0)))
                              (let
                                 ((sub$1_0 (- (- 1) _$1_1)))
                                 (let
                                    ((st_size.addr.0$1_0 sub$1_0))
                                    (let
                                       ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                       (=>
                                          cmp2$1_0
                                          (let
                                             ((retval.0$1_0 0))
                                             (let
                                                ((result$1 retval.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (fd$2_0 fd$2_0_old)
                                                 (file$2_0 file$2_0_old)
                                                 (st_size$2_0 st_size$2_0_old))
                                                (let
                                                   ((st_ino$2_0 st_ino$2_0_old)
                                                    (flag$2_0 flag$2_0_old)
                                                    (errno$2_0 errno$2_0_old)
                                                    (fstatat$2_0 fstatat$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (cmp$2_0 (= st_size$2_0 (- 1))))
                                                   (=>
                                                      cmp$2_0
                                                      (let
                                                         ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                         (let
                                                            ((cmp1$2_0 (distinct _$2_0 0)))
                                                            (=>
                                                               (not cmp1$2_0)
                                                               (let
                                                                  ((st_size.addr.0$2_0 st_size$2_0))
                                                                  (let
                                                                     ((st_ino.addr.0$2_0 st_ino$2_0)
                                                                      (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                                     (=>
                                                                        (not cmp2$2_0)
                                                                        (let
                                                                           ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                            (retval.0$2_0 (- 1)))
                                                                           (let
                                                                              ((result$2 retval.0$2_0)
                                                                               (HEAP$2_res HEAP$2))
                                                                              (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           cmp1$1_0
                           (let
                              ((_$1_1 (select HEAP$1 errno$1_0)))
                              (let
                                 ((sub$1_0 (- (- 1) _$1_1)))
                                 (let
                                    ((st_size.addr.0$1_0 sub$1_0))
                                    (let
                                       ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                       (=>
                                          cmp2$1_0
                                          (let
                                             ((retval.0$1_0 0))
                                             (let
                                                ((result$1 retval.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (fd$2_0 fd$2_0_old)
                                                 (file$2_0 file$2_0_old)
                                                 (st_size$2_0 st_size$2_0_old))
                                                (let
                                                   ((st_ino$2_0 st_ino$2_0_old)
                                                    (flag$2_0 flag$2_0_old)
                                                    (errno$2_0 errno$2_0_old)
                                                    (fstatat$2_0 fstatat$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (cmp$2_0 (= st_size$2_0 (- 1))))
                                                   (=>
                                                      (not cmp$2_0)
                                                      (let
                                                         ((st_size.addr.0$2_0 st_size$2_0))
                                                         (let
                                                            ((st_ino.addr.0$2_0 st_ino$2_0)
                                                             (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                            (=>
                                                               cmp2$2_0
                                                               (let
                                                                  ((retval.0$2_0 0))
                                                                  (let
                                                                     ((result$2 retval.0$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           cmp1$1_0
                           (let
                              ((_$1_1 (select HEAP$1 errno$1_0)))
                              (let
                                 ((sub$1_0 (- (- 1) _$1_1)))
                                 (let
                                    ((st_size.addr.0$1_0 sub$1_0))
                                    (let
                                       ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                       (=>
                                          cmp2$1_0
                                          (let
                                             ((retval.0$1_0 0))
                                             (let
                                                ((result$1 retval.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (fd$2_0 fd$2_0_old)
                                                 (file$2_0 file$2_0_old)
                                                 (st_size$2_0 st_size$2_0_old))
                                                (let
                                                   ((st_ino$2_0 st_ino$2_0_old)
                                                    (flag$2_0 flag$2_0_old)
                                                    (errno$2_0 errno$2_0_old)
                                                    (fstatat$2_0 fstatat$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (cmp$2_0 (= st_size$2_0 (- 1))))
                                                   (=>
                                                      (not cmp$2_0)
                                                      (let
                                                         ((st_size.addr.0$2_0 st_size$2_0))
                                                         (let
                                                            ((st_ino.addr.0$2_0 st_ino$2_0)
                                                             (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                            (=>
                                                               (not cmp2$2_0)
                                                               (let
                                                                  ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                   (retval.0$2_0 (- 1)))
                                                                  (let
                                                                     ((result$2 retval.0$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           cmp1$1_0
                           (let
                              ((_$1_1 (select HEAP$1 errno$1_0)))
                              (let
                                 ((sub$1_0 (- (- 1) _$1_1)))
                                 (let
                                    ((st_size.addr.0$1_0 sub$1_0))
                                    (let
                                       ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                       (=>
                                          (not cmp2$1_0)
                                          (let
                                             ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                                             (let
                                                ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                                 (retval.0$1_0 (- 1)))
                                                (let
                                                   ((result$1 retval.0$1_0)
                                                    (HEAP$1_res HEAP$1)
                                                    (fd$2_0 fd$2_0_old)
                                                    (file$2_0 file$2_0_old)
                                                    (st_size$2_0 st_size$2_0_old))
                                                   (let
                                                      ((st_ino$2_0 st_ino$2_0_old)
                                                       (flag$2_0 flag$2_0_old)
                                                       (errno$2_0 errno$2_0_old)
                                                       (fstatat$2_0 fstatat$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (= st_size$2_0 (- 1))))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                            (let
                                                               ((cmp1$2_0 (distinct _$2_0 0)))
                                                               (=>
                                                                  cmp1$2_0
                                                                  (let
                                                                     ((_$2_1 (select HEAP$2 errno$2_0))
                                                                      (st_size.addr.0$2_0 (- 2)))
                                                                     (let
                                                                        ((st_ino.addr.0$2_0 _$2_1)
                                                                         (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                                        (=>
                                                                           cmp2$2_0
                                                                           (let
                                                                              ((retval.0$2_0 0))
                                                                              (let
                                                                                 ((result$2 retval.0$2_0)
                                                                                  (HEAP$2_res HEAP$2))
                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           cmp1$1_0
                           (let
                              ((_$1_1 (select HEAP$1 errno$1_0)))
                              (let
                                 ((sub$1_0 (- (- 1) _$1_1)))
                                 (let
                                    ((st_size.addr.0$1_0 sub$1_0))
                                    (let
                                       ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                       (=>
                                          (not cmp2$1_0)
                                          (let
                                             ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                                             (let
                                                ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                                 (retval.0$1_0 (- 1)))
                                                (let
                                                   ((result$1 retval.0$1_0)
                                                    (HEAP$1_res HEAP$1)
                                                    (fd$2_0 fd$2_0_old)
                                                    (file$2_0 file$2_0_old)
                                                    (st_size$2_0 st_size$2_0_old))
                                                   (let
                                                      ((st_ino$2_0 st_ino$2_0_old)
                                                       (flag$2_0 flag$2_0_old)
                                                       (errno$2_0 errno$2_0_old)
                                                       (fstatat$2_0 fstatat$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (= st_size$2_0 (- 1))))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                            (let
                                                               ((cmp1$2_0 (distinct _$2_0 0)))
                                                               (=>
                                                                  cmp1$2_0
                                                                  (let
                                                                     ((_$2_1 (select HEAP$2 errno$2_0))
                                                                      (st_size.addr.0$2_0 (- 2)))
                                                                     (let
                                                                        ((st_ino.addr.0$2_0 _$2_1)
                                                                         (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                                        (=>
                                                                           (not cmp2$2_0)
                                                                           (let
                                                                              ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                               (retval.0$2_0 (- 1)))
                                                                              (let
                                                                                 ((result$2 retval.0$2_0)
                                                                                  (HEAP$2_res HEAP$2))
                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           cmp1$1_0
                           (let
                              ((_$1_1 (select HEAP$1 errno$1_0)))
                              (let
                                 ((sub$1_0 (- (- 1) _$1_1)))
                                 (let
                                    ((st_size.addr.0$1_0 sub$1_0))
                                    (let
                                       ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                       (=>
                                          (not cmp2$1_0)
                                          (let
                                             ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                                             (let
                                                ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                                 (retval.0$1_0 (- 1)))
                                                (let
                                                   ((result$1 retval.0$1_0)
                                                    (HEAP$1_res HEAP$1)
                                                    (fd$2_0 fd$2_0_old)
                                                    (file$2_0 file$2_0_old)
                                                    (st_size$2_0 st_size$2_0_old))
                                                   (let
                                                      ((st_ino$2_0 st_ino$2_0_old)
                                                       (flag$2_0 flag$2_0_old)
                                                       (errno$2_0 errno$2_0_old)
                                                       (fstatat$2_0 fstatat$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (= st_size$2_0 (- 1))))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                            (let
                                                               ((cmp1$2_0 (distinct _$2_0 0)))
                                                               (=>
                                                                  (not cmp1$2_0)
                                                                  (let
                                                                     ((st_size.addr.0$2_0 st_size$2_0))
                                                                     (let
                                                                        ((st_ino.addr.0$2_0 st_ino$2_0)
                                                                         (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                                        (=>
                                                                           cmp2$2_0
                                                                           (let
                                                                              ((retval.0$2_0 0))
                                                                              (let
                                                                                 ((result$2 retval.0$2_0)
                                                                                  (HEAP$2_res HEAP$2))
                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           cmp1$1_0
                           (let
                              ((_$1_1 (select HEAP$1 errno$1_0)))
                              (let
                                 ((sub$1_0 (- (- 1) _$1_1)))
                                 (let
                                    ((st_size.addr.0$1_0 sub$1_0))
                                    (let
                                       ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                       (=>
                                          (not cmp2$1_0)
                                          (let
                                             ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                                             (let
                                                ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                                 (retval.0$1_0 (- 1)))
                                                (let
                                                   ((result$1 retval.0$1_0)
                                                    (HEAP$1_res HEAP$1)
                                                    (fd$2_0 fd$2_0_old)
                                                    (file$2_0 file$2_0_old)
                                                    (st_size$2_0 st_size$2_0_old))
                                                   (let
                                                      ((st_ino$2_0 st_ino$2_0_old)
                                                       (flag$2_0 flag$2_0_old)
                                                       (errno$2_0 errno$2_0_old)
                                                       (fstatat$2_0 fstatat$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (= st_size$2_0 (- 1))))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                            (let
                                                               ((cmp1$2_0 (distinct _$2_0 0)))
                                                               (=>
                                                                  (not cmp1$2_0)
                                                                  (let
                                                                     ((st_size.addr.0$2_0 st_size$2_0))
                                                                     (let
                                                                        ((st_ino.addr.0$2_0 st_ino$2_0)
                                                                         (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                                        (=>
                                                                           (not cmp2$2_0)
                                                                           (let
                                                                              ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                               (retval.0$2_0 (- 1)))
                                                                              (let
                                                                                 ((result$2 retval.0$2_0)
                                                                                  (HEAP$2_res HEAP$2))
                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           cmp1$1_0
                           (let
                              ((_$1_1 (select HEAP$1 errno$1_0)))
                              (let
                                 ((sub$1_0 (- (- 1) _$1_1)))
                                 (let
                                    ((st_size.addr.0$1_0 sub$1_0))
                                    (let
                                       ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                       (=>
                                          (not cmp2$1_0)
                                          (let
                                             ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                                             (let
                                                ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                                 (retval.0$1_0 (- 1)))
                                                (let
                                                   ((result$1 retval.0$1_0)
                                                    (HEAP$1_res HEAP$1)
                                                    (fd$2_0 fd$2_0_old)
                                                    (file$2_0 file$2_0_old)
                                                    (st_size$2_0 st_size$2_0_old))
                                                   (let
                                                      ((st_ino$2_0 st_ino$2_0_old)
                                                       (flag$2_0 flag$2_0_old)
                                                       (errno$2_0 errno$2_0_old)
                                                       (fstatat$2_0 fstatat$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (= st_size$2_0 (- 1))))
                                                      (=>
                                                         (not cmp$2_0)
                                                         (let
                                                            ((st_size.addr.0$2_0 st_size$2_0))
                                                            (let
                                                               ((st_ino.addr.0$2_0 st_ino$2_0)
                                                                (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                               (=>
                                                                  cmp2$2_0
                                                                  (let
                                                                     ((retval.0$2_0 0))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           cmp1$1_0
                           (let
                              ((_$1_1 (select HEAP$1 errno$1_0)))
                              (let
                                 ((sub$1_0 (- (- 1) _$1_1)))
                                 (let
                                    ((st_size.addr.0$1_0 sub$1_0))
                                    (let
                                       ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                       (=>
                                          (not cmp2$1_0)
                                          (let
                                             ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                                             (let
                                                ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                                 (retval.0$1_0 (- 1)))
                                                (let
                                                   ((result$1 retval.0$1_0)
                                                    (HEAP$1_res HEAP$1)
                                                    (fd$2_0 fd$2_0_old)
                                                    (file$2_0 file$2_0_old)
                                                    (st_size$2_0 st_size$2_0_old))
                                                   (let
                                                      ((st_ino$2_0 st_ino$2_0_old)
                                                       (flag$2_0 flag$2_0_old)
                                                       (errno$2_0 errno$2_0_old)
                                                       (fstatat$2_0 fstatat$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (cmp$2_0 (= st_size$2_0 (- 1))))
                                                      (=>
                                                         (not cmp$2_0)
                                                         (let
                                                            ((st_size.addr.0$2_0 st_size$2_0))
                                                            (let
                                                               ((st_ino.addr.0$2_0 st_ino$2_0)
                                                                (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                               (=>
                                                                  (not cmp2$2_0)
                                                                  (let
                                                                     ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                      (retval.0$2_0 (- 1)))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           (not cmp1$1_0)
                           (let
                              ((st_size.addr.0$1_0 st_size$1_0))
                              (let
                                 ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                 (=>
                                    cmp2$1_0
                                    (let
                                       ((retval.0$1_0 0))
                                       (let
                                          ((result$1 retval.0$1_0)
                                           (HEAP$1_res HEAP$1)
                                           (fd$2_0 fd$2_0_old)
                                           (file$2_0 file$2_0_old)
                                           (st_size$2_0 st_size$2_0_old))
                                          (let
                                             ((st_ino$2_0 st_ino$2_0_old)
                                              (flag$2_0 flag$2_0_old)
                                              (errno$2_0 errno$2_0_old)
                                              (fstatat$2_0 fstatat$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (cmp$2_0 (= st_size$2_0 (- 1))))
                                             (=>
                                                cmp$2_0
                                                (let
                                                   ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                   (let
                                                      ((cmp1$2_0 (distinct _$2_0 0)))
                                                      (=>
                                                         cmp1$2_0
                                                         (let
                                                            ((_$2_1 (select HEAP$2 errno$2_0))
                                                             (st_size.addr.0$2_0 (- 2)))
                                                            (let
                                                               ((st_ino.addr.0$2_0 _$2_1)
                                                                (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                               (=>
                                                                  cmp2$2_0
                                                                  (let
                                                                     ((retval.0$2_0 0))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           (not cmp1$1_0)
                           (let
                              ((st_size.addr.0$1_0 st_size$1_0))
                              (let
                                 ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                 (=>
                                    cmp2$1_0
                                    (let
                                       ((retval.0$1_0 0))
                                       (let
                                          ((result$1 retval.0$1_0)
                                           (HEAP$1_res HEAP$1)
                                           (fd$2_0 fd$2_0_old)
                                           (file$2_0 file$2_0_old)
                                           (st_size$2_0 st_size$2_0_old))
                                          (let
                                             ((st_ino$2_0 st_ino$2_0_old)
                                              (flag$2_0 flag$2_0_old)
                                              (errno$2_0 errno$2_0_old)
                                              (fstatat$2_0 fstatat$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (cmp$2_0 (= st_size$2_0 (- 1))))
                                             (=>
                                                cmp$2_0
                                                (let
                                                   ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                   (let
                                                      ((cmp1$2_0 (distinct _$2_0 0)))
                                                      (=>
                                                         cmp1$2_0
                                                         (let
                                                            ((_$2_1 (select HEAP$2 errno$2_0))
                                                             (st_size.addr.0$2_0 (- 2)))
                                                            (let
                                                               ((st_ino.addr.0$2_0 _$2_1)
                                                                (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                               (=>
                                                                  (not cmp2$2_0)
                                                                  (let
                                                                     ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                      (retval.0$2_0 (- 1)))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           (not cmp1$1_0)
                           (let
                              ((st_size.addr.0$1_0 st_size$1_0))
                              (let
                                 ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                 (=>
                                    cmp2$1_0
                                    (let
                                       ((retval.0$1_0 0))
                                       (let
                                          ((result$1 retval.0$1_0)
                                           (HEAP$1_res HEAP$1)
                                           (fd$2_0 fd$2_0_old)
                                           (file$2_0 file$2_0_old)
                                           (st_size$2_0 st_size$2_0_old))
                                          (let
                                             ((st_ino$2_0 st_ino$2_0_old)
                                              (flag$2_0 flag$2_0_old)
                                              (errno$2_0 errno$2_0_old)
                                              (fstatat$2_0 fstatat$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (cmp$2_0 (= st_size$2_0 (- 1))))
                                             (=>
                                                cmp$2_0
                                                (let
                                                   ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                   (let
                                                      ((cmp1$2_0 (distinct _$2_0 0)))
                                                      (=>
                                                         (not cmp1$2_0)
                                                         (let
                                                            ((st_size.addr.0$2_0 st_size$2_0))
                                                            (let
                                                               ((st_ino.addr.0$2_0 st_ino$2_0)
                                                                (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                               (=>
                                                                  cmp2$2_0
                                                                  (let
                                                                     ((retval.0$2_0 0))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           (not cmp1$1_0)
                           (let
                              ((st_size.addr.0$1_0 st_size$1_0))
                              (let
                                 ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                 (=>
                                    cmp2$1_0
                                    (let
                                       ((retval.0$1_0 0))
                                       (let
                                          ((result$1 retval.0$1_0)
                                           (HEAP$1_res HEAP$1)
                                           (fd$2_0 fd$2_0_old)
                                           (file$2_0 file$2_0_old)
                                           (st_size$2_0 st_size$2_0_old))
                                          (let
                                             ((st_ino$2_0 st_ino$2_0_old)
                                              (flag$2_0 flag$2_0_old)
                                              (errno$2_0 errno$2_0_old)
                                              (fstatat$2_0 fstatat$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (cmp$2_0 (= st_size$2_0 (- 1))))
                                             (=>
                                                cmp$2_0
                                                (let
                                                   ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                   (let
                                                      ((cmp1$2_0 (distinct _$2_0 0)))
                                                      (=>
                                                         (not cmp1$2_0)
                                                         (let
                                                            ((st_size.addr.0$2_0 st_size$2_0))
                                                            (let
                                                               ((st_ino.addr.0$2_0 st_ino$2_0)
                                                                (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                               (=>
                                                                  (not cmp2$2_0)
                                                                  (let
                                                                     ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                      (retval.0$2_0 (- 1)))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           (not cmp1$1_0)
                           (let
                              ((st_size.addr.0$1_0 st_size$1_0))
                              (let
                                 ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                 (=>
                                    cmp2$1_0
                                    (let
                                       ((retval.0$1_0 0))
                                       (let
                                          ((result$1 retval.0$1_0)
                                           (HEAP$1_res HEAP$1)
                                           (fd$2_0 fd$2_0_old)
                                           (file$2_0 file$2_0_old)
                                           (st_size$2_0 st_size$2_0_old))
                                          (let
                                             ((st_ino$2_0 st_ino$2_0_old)
                                              (flag$2_0 flag$2_0_old)
                                              (errno$2_0 errno$2_0_old)
                                              (fstatat$2_0 fstatat$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (cmp$2_0 (= st_size$2_0 (- 1))))
                                             (=>
                                                (not cmp$2_0)
                                                (let
                                                   ((st_size.addr.0$2_0 st_size$2_0))
                                                   (let
                                                      ((st_ino.addr.0$2_0 st_ino$2_0)
                                                       (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                      (=>
                                                         cmp2$2_0
                                                         (let
                                                            ((retval.0$2_0 0))
                                                            (let
                                                               ((result$2 retval.0$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           (not cmp1$1_0)
                           (let
                              ((st_size.addr.0$1_0 st_size$1_0))
                              (let
                                 ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                 (=>
                                    cmp2$1_0
                                    (let
                                       ((retval.0$1_0 0))
                                       (let
                                          ((result$1 retval.0$1_0)
                                           (HEAP$1_res HEAP$1)
                                           (fd$2_0 fd$2_0_old)
                                           (file$2_0 file$2_0_old)
                                           (st_size$2_0 st_size$2_0_old))
                                          (let
                                             ((st_ino$2_0 st_ino$2_0_old)
                                              (flag$2_0 flag$2_0_old)
                                              (errno$2_0 errno$2_0_old)
                                              (fstatat$2_0 fstatat$2_0_old)
                                              (HEAP$2 HEAP$2_old)
                                              (cmp$2_0 (= st_size$2_0 (- 1))))
                                             (=>
                                                (not cmp$2_0)
                                                (let
                                                   ((st_size.addr.0$2_0 st_size$2_0))
                                                   (let
                                                      ((st_ino.addr.0$2_0 st_ino$2_0)
                                                       (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                      (=>
                                                         (not cmp2$2_0)
                                                         (let
                                                            ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                             (retval.0$2_0 (- 1)))
                                                            (let
                                                               ((result$2 retval.0$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           (not cmp1$1_0)
                           (let
                              ((st_size.addr.0$1_0 st_size$1_0))
                              (let
                                 ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                                       (let
                                          ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                           (retval.0$1_0 (- 1)))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (fd$2_0 fd$2_0_old)
                                              (file$2_0 file$2_0_old)
                                              (st_size$2_0 st_size$2_0_old))
                                             (let
                                                ((st_ino$2_0 st_ino$2_0_old)
                                                 (flag$2_0 flag$2_0_old)
                                                 (errno$2_0 errno$2_0_old)
                                                 (fstatat$2_0 fstatat$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (cmp$2_0 (= st_size$2_0 (- 1))))
                                                (=>
                                                   cmp$2_0
                                                   (let
                                                      ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                      (let
                                                         ((cmp1$2_0 (distinct _$2_0 0)))
                                                         (=>
                                                            cmp1$2_0
                                                            (let
                                                               ((_$2_1 (select HEAP$2 errno$2_0))
                                                                (st_size.addr.0$2_0 (- 2)))
                                                               (let
                                                                  ((st_ino.addr.0$2_0 _$2_1)
                                                                   (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                                  (=>
                                                                     cmp2$2_0
                                                                     (let
                                                                        ((retval.0$2_0 0))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           (not cmp1$1_0)
                           (let
                              ((st_size.addr.0$1_0 st_size$1_0))
                              (let
                                 ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                                       (let
                                          ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                           (retval.0$1_0 (- 1)))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (fd$2_0 fd$2_0_old)
                                              (file$2_0 file$2_0_old)
                                              (st_size$2_0 st_size$2_0_old))
                                             (let
                                                ((st_ino$2_0 st_ino$2_0_old)
                                                 (flag$2_0 flag$2_0_old)
                                                 (errno$2_0 errno$2_0_old)
                                                 (fstatat$2_0 fstatat$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (cmp$2_0 (= st_size$2_0 (- 1))))
                                                (=>
                                                   cmp$2_0
                                                   (let
                                                      ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                      (let
                                                         ((cmp1$2_0 (distinct _$2_0 0)))
                                                         (=>
                                                            cmp1$2_0
                                                            (let
                                                               ((_$2_1 (select HEAP$2 errno$2_0))
                                                                (st_size.addr.0$2_0 (- 2)))
                                                               (let
                                                                  ((st_ino.addr.0$2_0 _$2_1)
                                                                   (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                                  (=>
                                                                     (not cmp2$2_0)
                                                                     (let
                                                                        ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                         (retval.0$2_0 (- 1)))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           (not cmp1$1_0)
                           (let
                              ((st_size.addr.0$1_0 st_size$1_0))
                              (let
                                 ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                                       (let
                                          ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                           (retval.0$1_0 (- 1)))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (fd$2_0 fd$2_0_old)
                                              (file$2_0 file$2_0_old)
                                              (st_size$2_0 st_size$2_0_old))
                                             (let
                                                ((st_ino$2_0 st_ino$2_0_old)
                                                 (flag$2_0 flag$2_0_old)
                                                 (errno$2_0 errno$2_0_old)
                                                 (fstatat$2_0 fstatat$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (cmp$2_0 (= st_size$2_0 (- 1))))
                                                (=>
                                                   cmp$2_0
                                                   (let
                                                      ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                      (let
                                                         ((cmp1$2_0 (distinct _$2_0 0)))
                                                         (=>
                                                            (not cmp1$2_0)
                                                            (let
                                                               ((st_size.addr.0$2_0 st_size$2_0))
                                                               (let
                                                                  ((st_ino.addr.0$2_0 st_ino$2_0)
                                                                   (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                                  (=>
                                                                     cmp2$2_0
                                                                     (let
                                                                        ((retval.0$2_0 0))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           (not cmp1$1_0)
                           (let
                              ((st_size.addr.0$1_0 st_size$1_0))
                              (let
                                 ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                                       (let
                                          ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                           (retval.0$1_0 (- 1)))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (fd$2_0 fd$2_0_old)
                                              (file$2_0 file$2_0_old)
                                              (st_size$2_0 st_size$2_0_old))
                                             (let
                                                ((st_ino$2_0 st_ino$2_0_old)
                                                 (flag$2_0 flag$2_0_old)
                                                 (errno$2_0 errno$2_0_old)
                                                 (fstatat$2_0 fstatat$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (cmp$2_0 (= st_size$2_0 (- 1))))
                                                (=>
                                                   cmp$2_0
                                                   (let
                                                      ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                                      (let
                                                         ((cmp1$2_0 (distinct _$2_0 0)))
                                                         (=>
                                                            (not cmp1$2_0)
                                                            (let
                                                               ((st_size.addr.0$2_0 st_size$2_0))
                                                               (let
                                                                  ((st_ino.addr.0$2_0 st_ino$2_0)
                                                                   (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                                  (=>
                                                                     (not cmp2$2_0)
                                                                     (let
                                                                        ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                         (retval.0$2_0 (- 1)))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           (not cmp1$1_0)
                           (let
                              ((st_size.addr.0$1_0 st_size$1_0))
                              (let
                                 ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                                       (let
                                          ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                           (retval.0$1_0 (- 1)))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (fd$2_0 fd$2_0_old)
                                              (file$2_0 file$2_0_old)
                                              (st_size$2_0 st_size$2_0_old))
                                             (let
                                                ((st_ino$2_0 st_ino$2_0_old)
                                                 (flag$2_0 flag$2_0_old)
                                                 (errno$2_0 errno$2_0_old)
                                                 (fstatat$2_0 fstatat$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (cmp$2_0 (= st_size$2_0 (- 1))))
                                                (=>
                                                   (not cmp$2_0)
                                                   (let
                                                      ((st_size.addr.0$2_0 st_size$2_0))
                                                      (let
                                                         ((st_ino.addr.0$2_0 st_ino$2_0)
                                                          (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                         (=>
                                                            cmp2$2_0
                                                            (let
                                                               ((retval.0$2_0 0))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  cmp$1_0
                  (let
                     ((_$1_0 (select HEAP$1 fstatat$1_0)))
                     (let
                        ((cmp1$1_0 (distinct _$1_0 0)))
                        (=>
                           (not cmp1$1_0)
                           (let
                              ((st_size.addr.0$1_0 st_size$1_0))
                              (let
                                 ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                                 (=>
                                    (not cmp2$1_0)
                                    (let
                                       ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                                       (let
                                          ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                           (retval.0$1_0 (- 1)))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (fd$2_0 fd$2_0_old)
                                              (file$2_0 file$2_0_old)
                                              (st_size$2_0 st_size$2_0_old))
                                             (let
                                                ((st_ino$2_0 st_ino$2_0_old)
                                                 (flag$2_0 flag$2_0_old)
                                                 (errno$2_0 errno$2_0_old)
                                                 (fstatat$2_0 fstatat$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (cmp$2_0 (= st_size$2_0 (- 1))))
                                                (=>
                                                   (not cmp$2_0)
                                                   (let
                                                      ((st_size.addr.0$2_0 st_size$2_0))
                                                      (let
                                                         ((st_ino.addr.0$2_0 st_ino$2_0)
                                                          (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                         (=>
                                                            (not cmp2$2_0)
                                                            (let
                                                               ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                (retval.0$2_0 (- 1)))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((st_size.addr.0$1_0 st_size$1_0))
                     (let
                        ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((retval.0$1_0 0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (fd$2_0 fd$2_0_old)
                                  (file$2_0 file$2_0_old)
                                  (st_size$2_0 st_size$2_0_old))
                                 (let
                                    ((st_ino$2_0 st_ino$2_0_old)
                                     (flag$2_0 flag$2_0_old)
                                     (errno$2_0 errno$2_0_old)
                                     (fstatat$2_0 fstatat$2_0_old)
                                     (HEAP$2 HEAP$2_old)
                                     (cmp$2_0 (= st_size$2_0 (- 1))))
                                    (=>
                                       cmp$2_0
                                       (let
                                          ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                          (let
                                             ((cmp1$2_0 (distinct _$2_0 0)))
                                             (=>
                                                cmp1$2_0
                                                (let
                                                   ((_$2_1 (select HEAP$2 errno$2_0))
                                                    (st_size.addr.0$2_0 (- 2)))
                                                   (let
                                                      ((st_ino.addr.0$2_0 _$2_1)
                                                       (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                      (=>
                                                         cmp2$2_0
                                                         (let
                                                            ((retval.0$2_0 0))
                                                            (let
                                                               ((result$2 retval.0$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((st_size.addr.0$1_0 st_size$1_0))
                     (let
                        ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((retval.0$1_0 0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (fd$2_0 fd$2_0_old)
                                  (file$2_0 file$2_0_old)
                                  (st_size$2_0 st_size$2_0_old))
                                 (let
                                    ((st_ino$2_0 st_ino$2_0_old)
                                     (flag$2_0 flag$2_0_old)
                                     (errno$2_0 errno$2_0_old)
                                     (fstatat$2_0 fstatat$2_0_old)
                                     (HEAP$2 HEAP$2_old)
                                     (cmp$2_0 (= st_size$2_0 (- 1))))
                                    (=>
                                       cmp$2_0
                                       (let
                                          ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                          (let
                                             ((cmp1$2_0 (distinct _$2_0 0)))
                                             (=>
                                                cmp1$2_0
                                                (let
                                                   ((_$2_1 (select HEAP$2 errno$2_0))
                                                    (st_size.addr.0$2_0 (- 2)))
                                                   (let
                                                      ((st_ino.addr.0$2_0 _$2_1)
                                                       (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                      (=>
                                                         (not cmp2$2_0)
                                                         (let
                                                            ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                             (retval.0$2_0 (- 1)))
                                                            (let
                                                               ((result$2 retval.0$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((st_size.addr.0$1_0 st_size$1_0))
                     (let
                        ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((retval.0$1_0 0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (fd$2_0 fd$2_0_old)
                                  (file$2_0 file$2_0_old)
                                  (st_size$2_0 st_size$2_0_old))
                                 (let
                                    ((st_ino$2_0 st_ino$2_0_old)
                                     (flag$2_0 flag$2_0_old)
                                     (errno$2_0 errno$2_0_old)
                                     (fstatat$2_0 fstatat$2_0_old)
                                     (HEAP$2 HEAP$2_old)
                                     (cmp$2_0 (= st_size$2_0 (- 1))))
                                    (=>
                                       cmp$2_0
                                       (let
                                          ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                          (let
                                             ((cmp1$2_0 (distinct _$2_0 0)))
                                             (=>
                                                (not cmp1$2_0)
                                                (let
                                                   ((st_size.addr.0$2_0 st_size$2_0))
                                                   (let
                                                      ((st_ino.addr.0$2_0 st_ino$2_0)
                                                       (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                      (=>
                                                         cmp2$2_0
                                                         (let
                                                            ((retval.0$2_0 0))
                                                            (let
                                                               ((result$2 retval.0$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((st_size.addr.0$1_0 st_size$1_0))
                     (let
                        ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((retval.0$1_0 0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (fd$2_0 fd$2_0_old)
                                  (file$2_0 file$2_0_old)
                                  (st_size$2_0 st_size$2_0_old))
                                 (let
                                    ((st_ino$2_0 st_ino$2_0_old)
                                     (flag$2_0 flag$2_0_old)
                                     (errno$2_0 errno$2_0_old)
                                     (fstatat$2_0 fstatat$2_0_old)
                                     (HEAP$2 HEAP$2_old)
                                     (cmp$2_0 (= st_size$2_0 (- 1))))
                                    (=>
                                       cmp$2_0
                                       (let
                                          ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                          (let
                                             ((cmp1$2_0 (distinct _$2_0 0)))
                                             (=>
                                                (not cmp1$2_0)
                                                (let
                                                   ((st_size.addr.0$2_0 st_size$2_0))
                                                   (let
                                                      ((st_ino.addr.0$2_0 st_ino$2_0)
                                                       (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                      (=>
                                                         (not cmp2$2_0)
                                                         (let
                                                            ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                             (retval.0$2_0 (- 1)))
                                                            (let
                                                               ((result$2 retval.0$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((st_size.addr.0$1_0 st_size$1_0))
                     (let
                        ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((retval.0$1_0 0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (fd$2_0 fd$2_0_old)
                                  (file$2_0 file$2_0_old)
                                  (st_size$2_0 st_size$2_0_old))
                                 (let
                                    ((st_ino$2_0 st_ino$2_0_old)
                                     (flag$2_0 flag$2_0_old)
                                     (errno$2_0 errno$2_0_old)
                                     (fstatat$2_0 fstatat$2_0_old)
                                     (HEAP$2 HEAP$2_old)
                                     (cmp$2_0 (= st_size$2_0 (- 1))))
                                    (=>
                                       (not cmp$2_0)
                                       (let
                                          ((st_size.addr.0$2_0 st_size$2_0))
                                          (let
                                             ((st_ino.addr.0$2_0 st_ino$2_0)
                                              (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                             (=>
                                                cmp2$2_0
                                                (let
                                                   ((retval.0$2_0 0))
                                                   (let
                                                      ((result$2 retval.0$2_0)
                                                       (HEAP$2_res HEAP$2))
                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((st_size.addr.0$1_0 st_size$1_0))
                     (let
                        ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                        (=>
                           cmp2$1_0
                           (let
                              ((retval.0$1_0 0))
                              (let
                                 ((result$1 retval.0$1_0)
                                  (HEAP$1_res HEAP$1)
                                  (fd$2_0 fd$2_0_old)
                                  (file$2_0 file$2_0_old)
                                  (st_size$2_0 st_size$2_0_old))
                                 (let
                                    ((st_ino$2_0 st_ino$2_0_old)
                                     (flag$2_0 flag$2_0_old)
                                     (errno$2_0 errno$2_0_old)
                                     (fstatat$2_0 fstatat$2_0_old)
                                     (HEAP$2 HEAP$2_old)
                                     (cmp$2_0 (= st_size$2_0 (- 1))))
                                    (=>
                                       (not cmp$2_0)
                                       (let
                                          ((st_size.addr.0$2_0 st_size$2_0))
                                          (let
                                             ((st_ino.addr.0$2_0 st_ino$2_0)
                                              (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                             (=>
                                                (not cmp2$2_0)
                                                (let
                                                   ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                    (retval.0$2_0 (- 1)))
                                                   (let
                                                      ((result$2 retval.0$2_0)
                                                       (HEAP$2_res HEAP$2))
                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((st_size.addr.0$1_0 st_size$1_0))
                     (let
                        ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                              (let
                                 ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                  (retval.0$1_0 (- 1)))
                                 (let
                                    ((result$1 retval.0$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (fd$2_0 fd$2_0_old)
                                     (file$2_0 file$2_0_old)
                                     (st_size$2_0 st_size$2_0_old))
                                    (let
                                       ((st_ino$2_0 st_ino$2_0_old)
                                        (flag$2_0 flag$2_0_old)
                                        (errno$2_0 errno$2_0_old)
                                        (fstatat$2_0 fstatat$2_0_old)
                                        (HEAP$2 HEAP$2_old)
                                        (cmp$2_0 (= st_size$2_0 (- 1))))
                                       (=>
                                          cmp$2_0
                                          (let
                                             ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                             (let
                                                ((cmp1$2_0 (distinct _$2_0 0)))
                                                (=>
                                                   cmp1$2_0
                                                   (let
                                                      ((_$2_1 (select HEAP$2 errno$2_0))
                                                       (st_size.addr.0$2_0 (- 2)))
                                                      (let
                                                         ((st_ino.addr.0$2_0 _$2_1)
                                                          (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                         (=>
                                                            cmp2$2_0
                                                            (let
                                                               ((retval.0$2_0 0))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((st_size.addr.0$1_0 st_size$1_0))
                     (let
                        ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                              (let
                                 ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                  (retval.0$1_0 (- 1)))
                                 (let
                                    ((result$1 retval.0$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (fd$2_0 fd$2_0_old)
                                     (file$2_0 file$2_0_old)
                                     (st_size$2_0 st_size$2_0_old))
                                    (let
                                       ((st_ino$2_0 st_ino$2_0_old)
                                        (flag$2_0 flag$2_0_old)
                                        (errno$2_0 errno$2_0_old)
                                        (fstatat$2_0 fstatat$2_0_old)
                                        (HEAP$2 HEAP$2_old)
                                        (cmp$2_0 (= st_size$2_0 (- 1))))
                                       (=>
                                          cmp$2_0
                                          (let
                                             ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                             (let
                                                ((cmp1$2_0 (distinct _$2_0 0)))
                                                (=>
                                                   cmp1$2_0
                                                   (let
                                                      ((_$2_1 (select HEAP$2 errno$2_0))
                                                       (st_size.addr.0$2_0 (- 2)))
                                                      (let
                                                         ((st_ino.addr.0$2_0 _$2_1)
                                                          (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                         (=>
                                                            (not cmp2$2_0)
                                                            (let
                                                               ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                (retval.0$2_0 (- 1)))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((st_size.addr.0$1_0 st_size$1_0))
                     (let
                        ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                              (let
                                 ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                  (retval.0$1_0 (- 1)))
                                 (let
                                    ((result$1 retval.0$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (fd$2_0 fd$2_0_old)
                                     (file$2_0 file$2_0_old)
                                     (st_size$2_0 st_size$2_0_old))
                                    (let
                                       ((st_ino$2_0 st_ino$2_0_old)
                                        (flag$2_0 flag$2_0_old)
                                        (errno$2_0 errno$2_0_old)
                                        (fstatat$2_0 fstatat$2_0_old)
                                        (HEAP$2 HEAP$2_old)
                                        (cmp$2_0 (= st_size$2_0 (- 1))))
                                       (=>
                                          cmp$2_0
                                          (let
                                             ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                             (let
                                                ((cmp1$2_0 (distinct _$2_0 0)))
                                                (=>
                                                   (not cmp1$2_0)
                                                   (let
                                                      ((st_size.addr.0$2_0 st_size$2_0))
                                                      (let
                                                         ((st_ino.addr.0$2_0 st_ino$2_0)
                                                          (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                         (=>
                                                            cmp2$2_0
                                                            (let
                                                               ((retval.0$2_0 0))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((st_size.addr.0$1_0 st_size$1_0))
                     (let
                        ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                              (let
                                 ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                  (retval.0$1_0 (- 1)))
                                 (let
                                    ((result$1 retval.0$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (fd$2_0 fd$2_0_old)
                                     (file$2_0 file$2_0_old)
                                     (st_size$2_0 st_size$2_0_old))
                                    (let
                                       ((st_ino$2_0 st_ino$2_0_old)
                                        (flag$2_0 flag$2_0_old)
                                        (errno$2_0 errno$2_0_old)
                                        (fstatat$2_0 fstatat$2_0_old)
                                        (HEAP$2 HEAP$2_old)
                                        (cmp$2_0 (= st_size$2_0 (- 1))))
                                       (=>
                                          cmp$2_0
                                          (let
                                             ((_$2_0 (select HEAP$2 fstatat$2_0)))
                                             (let
                                                ((cmp1$2_0 (distinct _$2_0 0)))
                                                (=>
                                                   (not cmp1$2_0)
                                                   (let
                                                      ((st_size.addr.0$2_0 st_size$2_0))
                                                      (let
                                                         ((st_ino.addr.0$2_0 st_ino$2_0)
                                                          (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                         (=>
                                                            (not cmp2$2_0)
                                                            (let
                                                               ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                                (retval.0$2_0 (- 1)))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((st_size.addr.0$1_0 st_size$1_0))
                     (let
                        ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                              (let
                                 ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                  (retval.0$1_0 (- 1)))
                                 (let
                                    ((result$1 retval.0$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (fd$2_0 fd$2_0_old)
                                     (file$2_0 file$2_0_old)
                                     (st_size$2_0 st_size$2_0_old))
                                    (let
                                       ((st_ino$2_0 st_ino$2_0_old)
                                        (flag$2_0 flag$2_0_old)
                                        (errno$2_0 errno$2_0_old)
                                        (fstatat$2_0 fstatat$2_0_old)
                                        (HEAP$2 HEAP$2_old)
                                        (cmp$2_0 (= st_size$2_0 (- 1))))
                                       (=>
                                          (not cmp$2_0)
                                          (let
                                             ((st_size.addr.0$2_0 st_size$2_0))
                                             (let
                                                ((st_ino.addr.0$2_0 st_ino$2_0)
                                                 (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                (=>
                                                   cmp2$2_0
                                                   (let
                                                      ((retval.0$2_0 0))
                                                      (let
                                                         ((result$2 retval.0$2_0)
                                                          (HEAP$2_res HEAP$2))
                                                         (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))
(assert
   (forall
      ((fd$1_0_old Int)
       (file$1_0_old Int)
       (st_size$1_0_old Int)
       (st_ino$1_0_old Int)
       (flag$1_0_old Int)
       (errno$1_0_old Int)
       (fstatat$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (fd$2_0_old Int)
       (file$2_0_old Int)
       (st_size$2_0_old Int)
       (st_ino$2_0_old Int)
       (flag$2_0_old Int)
       (errno$2_0_old Int)
       (fstatat$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV fd$1_0_old file$1_0_old st_size$1_0_old st_ino$1_0_old flag$1_0_old errno$1_0_old fstatat$1_0_old HEAP$1_old fd$2_0_old file$2_0_old st_size$2_0_old st_ino$2_0_old flag$2_0_old errno$2_0_old fstatat$2_0_old HEAP$2_old)
         (let
            ((fd$1_0 fd$1_0_old)
             (file$1_0 file$1_0_old)
             (st_size$1_0 st_size$1_0_old))
            (let
               ((st_ino$1_0 st_ino$1_0_old)
                (flag$1_0 flag$1_0_old)
                (errno$1_0 errno$1_0_old)
                (fstatat$1_0 fstatat$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (= st_size$1_0 (- 1))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((st_size.addr.0$1_0 st_size$1_0))
                     (let
                        ((cmp2$1_0 (<= 0 st_size.addr.0$1_0)))
                        (=>
                           (not cmp2$1_0)
                           (let
                              ((sub5$1_0 (- (- 1) st_size.addr.0$1_0)))
                              (let
                                 ((HEAP$1 (store HEAP$1 errno$1_0 sub5$1_0))
                                  (retval.0$1_0 (- 1)))
                                 (let
                                    ((result$1 retval.0$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (fd$2_0 fd$2_0_old)
                                     (file$2_0 file$2_0_old)
                                     (st_size$2_0 st_size$2_0_old))
                                    (let
                                       ((st_ino$2_0 st_ino$2_0_old)
                                        (flag$2_0 flag$2_0_old)
                                        (errno$2_0 errno$2_0_old)
                                        (fstatat$2_0 fstatat$2_0_old)
                                        (HEAP$2 HEAP$2_old)
                                        (cmp$2_0 (= st_size$2_0 (- 1))))
                                       (=>
                                          (not cmp$2_0)
                                          (let
                                             ((st_size.addr.0$2_0 st_size$2_0))
                                             (let
                                                ((st_ino.addr.0$2_0 st_ino$2_0)
                                                 (cmp2$2_0 (<= 0 st_size.addr.0$2_0)))
                                                (=>
                                                   (not cmp2$2_0)
                                                   (let
                                                      ((HEAP$2 (store HEAP$2 errno$2_0 st_ino.addr.0$2_0))
                                                       (retval.0$2_0 (- 1)))
                                                      (let
                                                         ((result$2 retval.0$2_0)
                                                          (HEAP$2_res HEAP$2))
                                                         (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))
(check-sat)
(get-model)
