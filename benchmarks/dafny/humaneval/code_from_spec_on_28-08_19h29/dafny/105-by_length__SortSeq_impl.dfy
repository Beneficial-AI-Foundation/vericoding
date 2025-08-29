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
predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate IsPermutation(s1: seq<int>, s2: seq<int>)
{
  |s1| == |s2| && multiset(s1) == multiset(s2)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeq(s: seq<int>) returns (sorted: seq<int>)
Sort elements. Ensures: the result is sorted according to the ordering relation; returns the correct size/count; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  requires true
  ensures |sorted| == |s|
  ensures IsSorted(sorted)
  ensures IsPermutation(s, sorted)
// </vc-spec>
// <vc-code>
{
  if |s| <= 1 {
    return s;
  }
  var arr := s;
  var n := |arr|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k, l :: 0 <= k < l < i && 0 <= l < n ==> arr[k] <= arr[l]
    invariant multiset(arr) == multiset(s)
  {
    var minIndex := i;
    var j := i + 1;
    while j < n
      invariant i <= minIndex < n
      invariant i <= j <= n
      invariant forall k :: i <= k < j && 0 <= k < n ==> arr[minIndex] <= arr[k]
      invariant multiset(arr) == multiset(s)
    {
      if arr[j] < arr[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := arr[i];
      arr := arr[i := arr[minIndex]];
      arr := arr[minIndex := temp];
    }
    i := i + 1;
  }
  return arr;
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