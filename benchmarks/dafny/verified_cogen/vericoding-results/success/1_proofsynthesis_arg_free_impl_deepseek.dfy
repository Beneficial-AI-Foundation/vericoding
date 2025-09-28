// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsThereAnOddNumber(n: int): bool 
  ensures IsThereAnOddNumber(n) ==> n > 0
{ n > 0 }
lemma OnlyOddNumbersAreChosen(n: int) returns (result: int)
  requires IsThereAnOddNumber(n)
  ensures result % 2 == 1
  ensures result > 0
  /* helper modified by LLM (iteration 5): Fixed ghost parameter issue and implementation */
{
  result := 1;
}
// </vc-helpers>

// <vc-spec>
method ChooseOdd()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed to properly handle ghost lemma call */
{
  ghost var res := OnlyOddNumbersAreChosen(10);
}
// </vc-code>
