// <vc-preamble>
function SumTo(arr: seq<int>): int
    decreases |arr|
{
    if |arr| == 0 then
        0
    else
        SumTo(arr[..|arr|-1]) + arr[|arr|-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove snoc property of SumTo via unfolding */
lemma SumTo_Snoc(s: seq<int>, x: int)
  ensures SumTo(s + [x]) == SumTo(s) + x
{
  assert |s + [x]| == |s| + 1;
  assert (s + [x])[..|s|] == s;
  assert (s + [x])[|s|] == x;
  assert |s + [x]| > 0;
  calc {
    SumTo(s + [x]);
    == { }
    SumTo((s + [x])[..|s + [x]| - 1]) + (s + [x])[|s + [x]| - 1];
    == { assert (s + [x])[..|s + [x]| - 1] == s; assert (s + [x])[|s + [x]| - 1] == x; }
    SumTo(s) + x;
  }
}
// </vc-helpers>

// <vc-spec>
method Sum(arr: array<int>) returns (sum: int)
    ensures SumTo(arr[..]) == sum
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented loop accumulating sum with invariant tying to SumTo and final asserts for postcondition */
  var n := arr.Length;
  var i := 0;
  sum := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sum == SumTo(arr[..i])
    decreases n - i
  {
    var preI := i;
    assert 0 <= preI < n;
    var a := arr[preI];
    SumTo_Snoc(arr[..preI], a);
    sum := sum + a;
    i := preI + 1;
    assert arr[..i] == arr[..preI] + [a];
    assert sum == SumTo(arr[..i]);
  }
  assert i == n;
  assert arr[..] == arr[..n];
  assert sum == SumTo(arr[..]);
}
// </vc-code>
