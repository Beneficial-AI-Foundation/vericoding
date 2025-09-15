// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 3): simplified to scan from right to left for rightmost violation */
  var i := |arr| - 1;
  while i >= 1
    invariant 0 <= i < |arr|
    invariant forall j :: i < j < |arr| ==> arr[j] >= arr[j - 1]
  {
    if arr[i] < arr[i - 1] {
      pos := i;
      return;
    }
    i := i - 1;
  }
  pos := -1;
}
// </vc-code>
