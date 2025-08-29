// <vc-helpers>
lemma SortedSeqBounds(s: seq<int>)
  requires forall x :: x in s ==> 1 <= x <= 9
  ensures var sorted := SortSeq(s); forall x :: x in sorted ==> 1 <= x <= 9
{
  var sorted := SortSeq(s);
  assert multiset(s) == multiset(sorted);
  forall x | x in sorted
    ensures 1 <= x <= 9
  {
    assert x in multiset(sorted);
    assert x in multiset(s);
    assert x in s;
  }
}

lemma ReversedSeqBounds(s: seq<int>)
  requires forall x :: x in s ==> 1 <= x <= 9
  ensures var rev := reverse(s); forall x :: x in rev ==> 1 <= x <= 9
{
  var rev := reverse(s);
  forall x | x in rev
    ensures 1 <= x <= 9
  {
    var k :| 0 <= k < |rev| && rev[k] == x;
    assert s[|s| - 1 - k] == x;
    assert x in s;
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
Sort elements. Ensures: the size is bounded; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  requires forall x :: x in arr ==> 1 <= x <= 9
  ensures |result| == |arr|
  ensures forall i :: 0 <= i < |result| ==> result[i] in {"One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"}
// </vc-spec>
// <vc-code>
{
  var sorted := SortSeq(arr);
  SortedSeqBounds(arr);
  var reversed := reverse(sorted);
  ReversedSeqBounds(sorted);
  
  result := [];
  var i := 0;
  while i < |reversed|
    invariant 0 <= i <= |reversed|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] in {"One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"}
  {
    var name := NumberToName(reversed[i]);
    result := result + [name];
    i := i + 1;
  }
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}
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