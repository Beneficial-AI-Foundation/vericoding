// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed as it was not needed */
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected loop bounds and invariants for selection sort */
{
  var arr := new int[|s|];
  for i := 0 to |s| - 1 {
    arr[i] := s[i];
  }

  var len := arr.Length;
  for i := 0 to len - 1 
    invariant 0 <= i <= len
    invariant forall k, l :: 0 <= k < l < i ==> arr[k] <= arr[l]
    invariant multiset(arr[0..len]) == multiset(s)
    decreases len - i
  {
    var minIndex := i;
    for j := i + 1 to len - 1
      invariant i <= j <= len
      invariant i <= minIndex < j 
      invariant forall k :: i <= k < j ==> arr[minIndex] <= arr[k]
      invariant multiset(arr[0..len]) == multiset(s)
      decreases len - j
    {
      if arr[j] < arr[minIndex]
      {
        minIndex := j;
      }
    }
    if minIndex != i
    {
      var temp := arr[i];
      arr[i] := arr[minIndex];
      arr[minIndex] := temp;
    }
  }

  sorted := arr[..];
}
// </vc-code>
