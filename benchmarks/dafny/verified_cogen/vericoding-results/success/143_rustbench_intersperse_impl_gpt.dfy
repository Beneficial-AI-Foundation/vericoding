// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): add generic concatenation lemma to aid verification */
function min(a: int, b: int): int { if a < b then a else b }
lemma ConcatIndexing<T>(s: seq<T>, t: seq<T>, i: int)
  ensures 0 <= i < |s| ==> (s + t)[i] == s[i]
  ensures |s| <= i < |s| + |t| ==> (s + t)[i] == t[i - |s|]
{ }
// </vc-helpers>

// <vc-spec>
method Intersperse(numbers: array<int>, delim: int) returns (res: seq<int>)
    ensures
        numbers.Length == 0 ==> |res| == 0
    ensures
        numbers.Length != 0 ==> |res| == 2 * numbers.Length - 1
    ensures
        forall i :: 0 <= i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
    ensures
        forall i :: 0 <= i < |res| && i % 2 == 1 ==> res[i] == delim
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build the interspersed sequence iteratively with invariants */
  if numbers.Length == 0 {
    res := [];
  } else {
    var n := numbers.Length;
    var res0: seq<int> := [numbers[0]];
    var k := 1;
    while k < n
      invariant n == numbers.Length
      invariant 1 <= k <= n
      invariant |res0| == 2 * k - 1
      invariant forall i :: 0 <= i < |res0| && i % 2 == 0 ==> res0[i] == numbers[i / 2]
      invariant forall i :: 0 <= i < |res0| && i % 2 == 1 ==> res0[i] == delim
      decreases n - k
    {
      res0 := res0 + [delim, numbers[k]];
      k := k + 1;
    }
    res := res0;
  }
}
// </vc-code>
