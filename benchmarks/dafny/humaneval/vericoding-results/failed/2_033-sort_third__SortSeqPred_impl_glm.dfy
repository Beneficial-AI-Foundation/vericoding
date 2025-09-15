// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ExtractValuesToSort(s: seq<int>, p: seq<bool>): seq<int>
  requires |s| == |p|
{
  if |s| == 0 then []
  else (if p[0] then [s[0]] else []) + ExtractValuesToSort(s[1..], p[1..])
}

/* helper modified by LLM (iteration 5): fixed syntax in SortSeq by properly formatting let binding */
function InsertSortedValues(original: seq<int>, sortedValues: seq<int>, p: seq<bool>): seq<int>
  requires |original| == |p| && CountTrue(p) == |sortedValues|
{
  if |original| == 0 then []
  else
    if p[0] then 
      [sortedValues[0]] + InsertSortedValues(original[1..], sortedValues[1..], p[1..])
    else
      [original[0]] + InsertSortedValues(original[1..], sortedValues, p[1..])
}

function CountTrue(p: seq<bool>): nat
{
  if |p| == 0 then 0
  else (if p[0] then 1 else 0) + CountTrue(p[1..])
}

/* helper modified by LLM (iteration 5): fixed syntax error by properly formatting let binding with in keyword */
function SortSeq(s: seq<int>): seq<int>
{
  if |s| <= 1 then s else
    var pivot := s[0];
    var less, greater := Partition(s[1..], pivot);
    SortSeq(less) + [pivot] + SortSeq(greater)
}

function Partition(s: seq<int>, pivot: int): (seq<int>, seq<int>)
{
  if |s| == 0 then ([], [])
  else
    var less, greater := Partition(s[1..], pivot);
    if s[0] <= pivot then ([s[0]] + less, greater)
    else (less, [s[0]] + greater)
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
{
  /* code modified by LLM (iteration 5): fixed helper function syntax and using properly formatted SortSeq */
  var valuesToSort := ExtractValuesToSort(s, p);
  var sortedValues := SortSeq(valuesToSort);
  sorted := InsertSortedValues(s, sortedValues, p);
}
// </vc-code>
