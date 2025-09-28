// <vc-preamble>
function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): identity helper for sequences */
function IdSeq(s: seq<int>): seq<int> {
  s
}
// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): iterative reversal with loop and invariants */
  var n := |s|;
  var i := n - 1;
  rev := [];
  while i >= 0
    invariant 0 <= i + 1 <= n
    invariant |rev| == n - (i + 1)
    invariant forall j :: 0 <= j < |rev| ==> rev[j] == s[n - 1 - j]
    decreases i + 1
  {
    rev := rev + [s[i]];
    i := i - 1;
  }
}
// </vc-code>
