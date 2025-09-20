-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cardsAndPero (s : String) : List Int := sorry

theorem cardsAndPero_empty_string :
  cardsAndPero "" = [13,13,13,13] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cardsAndPero_three_pikes :
  cardsAndPero "P01P02P03" = [10,13,13,13] := sorry

theorem cardsAndPero_one_of_each :
  cardsAndPero "P01K01H01" = [12,12,12,13] := sorry

theorem cardsAndPero_duplicate_card :
  cardsAndPero "P01P01" = [-1,-1,-1,-1] := sorry

theorem cardsAndPero_all_suits :
  cardsAndPero "P01K02H03T04" = [12,12,12,12] := sorry
-- </vc-theorems>