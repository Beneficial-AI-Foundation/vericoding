// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple min function retained for completeness */
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method can_arrange(arr: seq<int>) returns (pos: int)

  requires |arr| > 0
  requires forall i, j :: 0 <= i < j < |arr| ==> arr[i] != arr[j]

  ensures pos == -1 ==> forall i :: 1 <= i < |arr| ==> arr[i] >= arr[i - 1]
  ensures pos >= 0 ==> 1 <= pos < |arr| && arr[pos] < arr[pos - 1]
  ensures pos >= 0 ==> forall i :: pos < i < |arr| ==> arr[i] >= arr[i - 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): scan from right to left to find first descent; added invariants and lexicographic decreases to verify */
  if |arr| == 1 {
    pos := -1;
  } else {
    var i := |arr| - 1;
    var p := -1;
    while i >= 1 && p == -1
      invariant 1 <= |arr|
      invariant -1 <= p < |arr|
      invariant 0 <= i < |arr|
      invariant p == -1 ==> forall k :: i < k < |arr| ==> arr[k] >= arr[k - 1]
      invariant p != -1 ==> forall k :: p < k < |arr| ==> arr[k] >= arr[k - 1]
      invariant p != -1 ==> 1 <= p < |arr| && arr[p] < arr[p - 1]
      decreases i, (if p == -1 then 1 else 0)
    {
      if arr[i] < arr[i - 1] {
        p := i;
      } else {
        i := i - 1;
      }
    }
    pos := p;
  }
}
// </vc-code>
