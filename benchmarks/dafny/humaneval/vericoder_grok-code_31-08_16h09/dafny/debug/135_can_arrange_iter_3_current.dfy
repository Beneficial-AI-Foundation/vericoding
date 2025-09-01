

// <vc-helpers>
{}
// </vc-helpers>

// <vc-spec>
method can_arrange(arr: seq<int>) returns (pos: int)
  // pre-conditions-start
  requires |arr| > 0
  requires forall i, j :: 0 <= i < j < |arr| ==> arr[i] != arr[j]
  // pre-conditions-end
  // post-conditions-start
  ensures pos == -1 ==> forall i :: 1 <= i < |arr| ==> arr[i] >= arr[i - 1]
  ensures pos >= 0 ==> 1 <= pos < |arr| && arr[pos] < arr[pos - 1]
  ensures pos >= 0 ==> forall i :: pos < i < |arr| ==> arr[i] >= arr[i - 1]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var pos := -1;
  var i := 1;
  while i < |arr| {
    if pos == -1 {
      if arr[i] < arr[i - 1] {
        pos := i;
      }
    } else {
      assert arr[i] >= arr[i - 1];
    }
    i := i + 1;
  }
}
// </vc-code>

