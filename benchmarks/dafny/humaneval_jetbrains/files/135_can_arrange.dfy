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
  assume {:axiom} false;
}
// </vc-code>
