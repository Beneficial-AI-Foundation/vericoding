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
{
  // impl-start
  var i := 1;
  pos := -1;
  while i < |arr|
    // invariants-start
    invariant 1 <= i <= |arr|
    invariant pos == -1 ==> forall j :: 1 <= j < i ==> arr[j] >= arr[j - 1]
    invariant pos >= 0 ==> 1 <= pos < i && arr[pos] < arr[pos - 1]
    invariant pos >= 0 ==> forall j :: pos < j < i ==> arr[j] >= arr[j - 1]
    // invariants-end
  {
    if arr[i] < arr[i - 1] {
      pos := i;
    }
    i := i + 1;
  }
  // impl-end
}
