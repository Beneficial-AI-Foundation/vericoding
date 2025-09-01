

// <vc-helpers>
// no additional helpers needed
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
  pos := -1;
  for i := 1 to |arr| {
    if arr[i] < arr[i - 1] {
      if pos == -1 {
        pos := i;
      } else {
        pos := -1;
        break;
      }
    }
  }
  if pos != -1 {
    // verify no descent after pos
    for i := pos + 1 to |arr| {
      assert arr[i] >= arr[i - 1];
    }
  }
}
// </vc-code>

