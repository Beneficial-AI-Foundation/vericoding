// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed multiset comprehension syntax */
function ExtractValuesByPredicate(s: seq<int>, p: seq<bool>): seq<int>
  requires |s| == |p|
  ensures |result| == count(p, true)
  ensures multiset(result) == multiset(s[i] | i := 0..|s| where p[i])
{
  if |s| == 0 then []
  else if p[0] then [s[0]] + ExtractValuesByPredicate(s[1..], p[1..])
  else ExtractValuesByPredicate(s[1..], p[1..])
}

function SortedInsert(sorted: seq<int>, x: int): seq<int>
  requires Sorted(sorted)
  ensures |result| == |sorted| + 1
  ensures multiset(result) == multiset(sorted) + {x}
  ensures Sorted(result)
{
  if |sorted| == 0 then [x]
  else if x <= sorted[0] then [x] + sorted
  else [sorted[0]] + SortedInsert(sorted[1..], x)
}

function count<T>(s: seq<T>, val: T): nat {
  if |s| == 0 then 0
  else (if s[0] == val then 1 else 0) + count(s[1..], val)
}

predicate Sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)

  requires |s| == |p|

  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Complete implementation with corrected multiset comprehension */
{
  // Extract values where p[i] is true
  var valuesToSort := ExtractValuesByPredicate(s, p);
  var sortedValues := SortSeq(valuesToSort);
  
  // Fill positions where p[i] is false with original values
  sorted := [];
  var sortedIndex := 0;
  
  for i := 0 to |s| - 1
    invariant |sorted| == i
    invariant sortedIndex <= |sortedValues|
    invariant multiset(sorted) == multiset(s[0..i])
  {
    if !p[i] {
      sorted := sorted + [s[i]];
    } else {
      sorted := sorted + [sortedValues[sortedIndex]];
      sortedIndex := sortedIndex + 1;
    }
  }
}

function SortSeq(s: seq<int>): seq<int>
  ensures |result| == |s|
  ensures multiset(result) == multiset(s)
  ensures Sorted(result)
{
  if |s| == 0 then []
  else SortedInsert(SortSeq(s[1..]), s[0])
}
// </vc-code>
