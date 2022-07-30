{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QproofZ45Zobjects where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List

-- proof-objects.empty-nat
d_empty'45'nat_2 :: [Integer]
d_empty'45'nat_2 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- proof-objects.empty-char
d_empty'45'char_4 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_empty'45'char_4
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- proof-objects.1-2-3-4
d_1'45'2'45'3'45'4_6 :: [Integer]
d_1'45'2'45'3'45'4_6
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (3 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (4 :: Integer))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- proof-objects.x-y-z
d_x'45'y'45'z_8 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_x'45'y'45'z_8
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'x')
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'y')
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'z')
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- proof-objects.length
d_length_12 :: () -> [AgdaAny] -> Integer
d_length_12 ~v0 v1 = du_length_12 v1
du_length_12 :: [AgdaAny] -> Integer
du_length_12 v0
  = case coe v0 of
      [] -> coe (0 :: Integer)
      (:) v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_length_12 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- proof-objects.app
d_app_20 :: () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d_app_20 ~v0 v1 v2 = du_app_20 v1 v2
du_app_20 :: [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du_app_20 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe du_app_20 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- proof-objects.rev
d_rev_32 :: () -> [AgdaAny] -> [AgdaAny]
d_rev_32 ~v0 v1 = du_rev_32 v1
du_rev_32 :: [AgdaAny] -> [AgdaAny]
du_rev_32 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             du_app_20 (coe du_rev_32 (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- proof-objects.rev-empty-nat-empty-nat
d_rev'45'empty'45'nat'45'empty'45'nat_38 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rev'45'empty'45'nat'45'empty'45'nat_38 = erased
-- proof-objects.rev-empty-char-empty-char
d_rev'45'empty'45'char'45'empty'45'char_40 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rev'45'empty'45'char'45'empty'45'char_40 = erased
-- proof-objects.rev-1-2-3-4-4-3-2-1
d_rev'45'1'45'2'45'3'45'4'45'4'45'3'45'2'45'1_42 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rev'45'1'45'2'45'3'45'4'45'4'45'3'45'2'45'1_42 = erased
-- proof-objects.rev-x-y-z-z-y-x
d_rev'45'x'45'y'45'z'45'z'45'y'45'x_44 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rev'45'x'45'y'45'z'45'z'45'y'45'x_44 = erased
-- proof-objects.length-1-2-3-4-OK
d_length'45'1'45'2'45'3'45'4'45'OK_46 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'1'45'2'45'3'45'4'45'OK_46 = erased
-- proof-objects.length-x-y-z-OK
d_length'45'x'45'y'45'z'45'OK_48 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'x'45'y'45'z'45'OK_48 = erased
-- proof-objects.app-nil-l
d_app'45'nil'45'l_54 ::
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'nil'45'l_54 = erased
-- proof-objects.cong
d_cong_68 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_68 = erased
-- proof-objects.app-nil-r
d_app'45'nil'45'r_76 ::
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'nil'45'r_76 = erased
-- proof-objects.sym
d_sym_90 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_90 = erased
-- proof-objects.app-nil-r-sym
d_app'45'nil'45'r'45'sym_96 ::
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'nil'45'r'45'sym_96 = erased
-- proof-objects.trans
d_trans_108 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_108 = erased
-- proof-objects.subst
d_subst_118 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_subst_118 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_subst_118 v5
du_subst_118 :: AgdaAny -> AgdaAny
du_subst_118 v0 = coe v0
-- proof-objects.app-nil-r′
d_app'45'nil'45'r'8242'_128 ::
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'nil'45'r'8242'_128 = erased
-- proof-objects.length-succ-r
d_length'45'succ'45'r_142 ::
  () ->
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'succ'45'r_142 = erased
-- proof-objects.rev-pres-length
d_rev'45'pres'45'length_160 ::
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rev'45'pres'45'length_160 = erased
