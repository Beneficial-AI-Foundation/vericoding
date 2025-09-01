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
lemma SortedAndReversedSorted(s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |s| ==> s[|s| - 1 - i] >= s[|s| - 1 - j]
{
}

function reverse_function(s: seq<int>): seq<int> {
  if |s| == 0 then []
  else reverse_function(s[1..]) + [s[0]]
}

lemma reverse_function_properties(s: seq<int>)
  ensures |reverse_function(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverse_function(s)[k] == s[|s| - 1 - k]
{
}

lemma reverse_function_preserves_multiset(s: seq<int>)
  ensures multiset(reverse_function(s)) == multiset(s)
{
}

method reverse_method(s: seq<int>) returns (rev: seq<int>)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
{
  rev := [];
  var i := |s| - 1;
  while i >= 0
    invariant -1 <= i < |s|
    invariant |rev| == |s| - 1 - i
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - k]
  {
    rev := rev + [s[i]];
    i := i - 1;
  }
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
{
  var sorted_s := SortSeq(s);
  var reversed := reverse_method(sorted_s);
  var res: seq<string> := [];
  var i := 0;
  while i < |reversed|
    invariant 0 <= i <= |reversed|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
    invariant |res| <= |s|
  {
    if 1 <= reversed[i] <= 9 {
      res := res + [NumberToName(reversed[i])];
    }
    i := i + 1;
  }
  return res;
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