

// <vc-helpers>
function reverse_seq(s: seq<int>) : seq<int>
  ensures |result| == |s|
  ensures forall k :: 0 <= k < |s| ==> result[k] == s[|s| - 1 - k]
{
    if |s| == 0 then s
    else reverse_seq(s[1..]) + [s[0]]
}
function min_element(s: seq<int>) : int {
    if |s| == 1 then s[0]
    else
        if s[0] <= min_element(s[1..]) then s[0]
        else min_element(s[1..])
}
function remove_first_occurrence(s: seq<int>, x: int) : seq<int> {
    if |s| == 0 then s
    else if s[0] == x then s[1..]
    else [s[0]] + remove_first_occurrence(s[1..], x)
}
function sort_non_decreasing(s: seq<int>) : seq<int>
  ensures |result| == |s|
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
{
    if |s| <= 1 then s
    else
        {
            let m = min_element(s);
            let rest = remove_first_occurrence(s, m);
            [m] + sort_non_decreasing(rest)
        }
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
// </vc-spec>
// <vc-code>
if |s| == 0 {
        s
      } else if ((s[0] + s[|s|-1]) % 2 == 0) {
        reverse_seq(sort_non_decreasing(s))
      } else {
        sort_non_decreasing(s)
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
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}