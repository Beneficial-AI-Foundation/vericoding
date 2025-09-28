// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [no changes, predicate is correct] */
predicate Sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}
// </vc-helpers>

// <vc-spec>
method BubbleSort(a: seq<int>) returns (result: seq<int>)
    ensures |result| == |a|
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    ensures multiset(a) == multiset(result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): [added assert to propagate postcondition of copy loop] */
  var n := |a|;
  var arr := new int[n];
  
  var k := 0;
  while k < n 
    invariant 0 <= k <= n
    invariant forall i :: 0 <= i < k ==> arr[i] == a[i]
  {
    arr[k] := a[k];
    k := k + 1;
  }

  assert arr[..] == a;

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant multiset(arr[..]) == multiset(a)
    invariant Sorted(arr[..i])
    invariant forall j, k :: 0 <= j < i && i <= k < n ==> arr[j] <= arr[k]
  {
    var j := n - 1;
    while j > i
      invariant i <= j < n
      invariant multiset(arr[..]) == multiset(a)
      invariant Sorted(arr[..i])
      invariant forall j_outer, k_outer :: 0 <= j_outer < i && i <= k_outer < n ==> arr[j_outer] <= arr[k_outer]
      invariant forall k :: j <= k < n ==> arr[j] <= arr[k]
    {
      if arr[j-1] > arr[j] {
        var tmp := arr[j-1];
        arr[j-1] := arr[j];
        arr[j] := tmp;
      }
      j := j - 1;
    }
    i := i + 1;
  }

  result := arr[..];
}
// </vc-code>
