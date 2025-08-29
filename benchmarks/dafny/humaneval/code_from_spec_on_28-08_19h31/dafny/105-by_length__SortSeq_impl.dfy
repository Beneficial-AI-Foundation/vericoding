method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma SortedMultisetPreservation(s: seq<int>, sorted: seq<int>)
  requires multiset(s) == multiset(sorted)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall k :: 0 <= k < |sorted| ==> sorted[k] in s
{
  var m := multiset(s);
  forall k | 0 <= k < |sorted|
  ensures sorted[k] in s
  {
    assert sorted[k] in m;
    assert sorted[k] in s;
  }
}

lemma MultisetPreservation(arr: array<int>, s: seq<int>, n: int)
  requires 0 <= n <= arr.Length
  requires n <= |s|
  requires forall k :: 0 <= k < n ==> arr[k] == s[k]
  ensures multiset(arr[..n]) == multiset(s[..n])
{
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
method SortSeqImpl(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  var n := |s|;
  if n == 0 {
    return [];
  }
  
  var arr := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> arr[k] == s[k]
  {
    arr[i] := s[i];
    i := i + 1;
  }
  
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant forall k, l :: 0 <= k < l < j ==> arr[k] <= arr[l]
    invariant multiset(arr[..]) == multiset(s[..])
  {
    if j == n - 1 {
      break;
    }
    var minIndex := j;
    var k := j + 1;
    while k < n
      invariant j <= minIndex < n
      invariant j <= k <= n
      invariant forall m :: j <= m < k ==> arr[minIndex] <= arr[m]
      invariant multiset(arr[..]) == multiset(s[..])
    {
      if arr[k] < arr[minIndex] {
        minIndex := k;
      }
      k := k + 1;
    }
    if minIndex != j {
      var temp := arr[j];
      arr[j] := arr[minIndex];
      arr[minIndex] := temp;
    }
    j := j + 1;
  }
  
  sorted := arr[..];
  assert multiset(sorted) == multiset(s[..]);
  return sorted;
}
// </vc-code>

method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}
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
// pure-end