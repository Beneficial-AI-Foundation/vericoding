

// <vc-helpers>
predicate SortedBetween(arr: seq<int>, start: int, end: int)
  requires 0 <= start <= end <= |arr|
{
  forall i, j :: start <= i < j < end ==> arr[i] <= arr[j]
}

lemma FindDescent(arr: seq<int>)
  requires |arr| > 0
  requires forall i, j :: 0 <= i < j < |arr| ==> arr[i] != arr[j]
  ensures exists pos :: 1 <= pos < |arr| && arr[pos] < arr[pos - 1] || 
           forall i :: 1 <= i < |arr| ==> arr[i] >= arr[i - 1]
{
  var k := 1;
  while k < |arr|
    invariant 1 <= k <= |arr|
    invariant forall i :: 1 <= i < k ==> arr[i] >= arr[i - 1]
  {
    if arr[k] < arr[k - 1] {
      return;
    }
    k := k + 1;
  }
}
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
  if |arr| == 1 {
    pos := -1;
    return;
  }
  
  var i := 1;
  while i < |arr|
    invariant 1 <= i <= |arr|
    invariant forall j :: 1 <= j < i ==> arr[j] >= arr[j - 1]
  {
    if arr[i] < arr[i - 1] {
      pos := i;
      return;
    }
    i := i + 1;
  }
  
  pos := -1;
}
// </vc-code>

