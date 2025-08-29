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
predicate sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate multiset_eq<T(==)>(s1: seq<T>, s2: seq<T>)
{
  multiset(s1) == multiset(s2)
}

lemma SwapPreservesMultiset(s: seq<int>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
}

lemma SwapPreservesSortedPrefix(s: seq<int>, k: int, i: int, j: int)
  requires 0 <= k <= i < j < |s|
  requires forall x, y :: 0 <= x < y < k ==> s[x] <= s[y]
  ensures forall x, y :: 0 <= x < y < k ==> s[i := s[j]][j := s[i]][x] <= s[i := s[j]][j := s[i]][y]
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeq(s: seq<int>) returns (sorted: seq<int>)
Sort elements. Ensures: the result is sorted according to the ordering relation; returns the correct size/count; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method SortSeq(s: seq<int>) returns (result: seq<int>)
  ensures |result| == |s|
  ensures sorted(result)
  ensures multiset_eq(result, s)
// </vc-spec>
// <vc-code>
{
  result := s;
  
  var i := 0;
  while i < |result|
    invariant 0 <= i <= |result|
    invariant |result| == |s|
    invariant multiset_eq(result, s)
    invariant forall x, y :: 0 <= x < y < i ==> result[x] <= result[y]
  {
    var j := i;
    while j > 0 && result[j-1] > result[j]
      invariant 0 <= j <= i
      invariant |result| == |s|
      invariant multiset_eq(result, s)
      invariant forall x, y :: 0 <= x < y < j ==> result[x] <= result[y]
      invariant forall x, y :: j < x < y <= i ==> result[x] <= result[y]
      invariant forall x :: 0 <= x < j ==> result[x] <= result[j]
    {
      SwapPreservesMultiset(result, j-1, j);
      SwapPreservesSortedPrefix(result, j-1, j-1, j);
      result := result[j-1 := result[j]][j := result[j-1]];
      j := j - 1;
    }
    i := i + 1;
  }
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