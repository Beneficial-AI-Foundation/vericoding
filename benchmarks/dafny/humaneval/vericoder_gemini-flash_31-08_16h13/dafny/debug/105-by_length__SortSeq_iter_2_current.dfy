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
function SortSeq(s: seq<int>) : seq<int>
  ensures forall i, j :: 0 <= i < j < |SortSeq(s)| ==> SortSeq(s)[i] <= SortSeq(s)[j]
  ensures |SortSeq(s)| == |s|
  ensures multiset(s) == multiset(SortSeq(s))
{
  if |s| <= 1 then s
  else
    var pivot := s[|s| / 2];
    var smaller := SortSeq(seq k | 0 <= k < |s| && s[k] < pivot :: s[k]);
    var larger := SortSeq(seq k | 0 <= k < |s| && s[k] > pivot :: s[k]);
    var equal := seq k | 0 <= k < |s| && s[k] == pivot :: s[k]);
    smaller + equal + larger
}

function reverse(s: seq<int>): seq<int>
  ensures |reverse(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverse(s)[k] == s[|s| - 1 - k]
{
  if |s| == 0 then []
  else
    [s[|s|-1]] + reverse(s[..|s|-1])
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
  var sorted_arr := SortSeq(s);
  return sorted_arr;
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