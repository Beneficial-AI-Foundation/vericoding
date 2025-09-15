// <vc-preamble>
function ThreeDistinct(s: string, i: int): bool
    requires 0 < i < |s| - 1
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
}
function Happy(s: string) : bool
{
    |s| >= 3 &&
    forall i :: 0 < i < |s| - 1 ==> ThreeDistinct(s, i)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Strengthen lemma to provide proper postcondition for ThreeDistinct equivalence */
function ThreeDistinctHelper(s: string, i: int): bool
  requires 0 < i < |s| - 1
{
  s[i - 1] != s[i] && s[i] != s[i + 1] && s[i - 1] != s[i + 1]
}

/* helper modified by LLM (iteration 4): Fix lemma to ensure ThreeDistinctHelper exactly matches ThreeDistinct */
lemma ValidateIndicesLemma(s: string, i: int)
  requires |s| >= 3 && 0 < i < |s| - 1
  ensures ThreeDistinctHelper(s, i) == ThreeDistinct(s, i)
{
}
// </vc-helpers>

// <vc-spec>
method IsHappy(s: string) returns (happy : bool)

    ensures happy <==> Happy(s)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Strengthen loop invariant to ensure complete verification */
{
  if |s| < 3 {
    happy := false;
  } else {
    var allHappy := true;
    var i := 1;
    while i < |s| - 1
      invariant 1 <= i <= |s| - 1
      invariant allHappy == forall j :: 1 <= j < i ==> ThreeDistinctHelper(s, j)
      invariant allHappy <==> forall j :: 1 <= j < i ==> ThreeDistinct(s, j)
    {
      ValidateIndicesLemma(s, i);
      if !ThreeDistinctHelper(s, i) {
        allHappy := false;
        break;
      }
      i := i + 1;
    }
    happy := allHappy;
  }
}
// </vc-code>
