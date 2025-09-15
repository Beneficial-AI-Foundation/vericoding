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
/* helper modified by LLM (iteration 2): simplified helper predicate to avoid non-compilable quantifiers */
predicate ValidCenter(s: string, i: int) { 0 < i < |s| - 1 }
// </vc-helpers>

// <vc-spec>
method IsHappy(s: string) returns (happy : bool)

    ensures happy <==> Happy(s)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute happiness via loop without using non-compilable quantifiers in code */
  var n := |s|;
  if n < 3 {
    happy := false;
  } else {
    var ok := true;
    var i := 1;
    while i <= n - 2
      invariant 1 <= i <= n - 1
      invariant ok == (forall j :: 0 < j < i ==> ThreeDistinct(s, j))
      decreases n - 1 - i
    {
      assert 0 < i < n - 1;
      assert ThreeDistinct(s, i) <==> ((s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1]));
      ok := ok && ((s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1]));
      i := i + 1;
    }
    happy := ok;
  }
}
// </vc-code>
