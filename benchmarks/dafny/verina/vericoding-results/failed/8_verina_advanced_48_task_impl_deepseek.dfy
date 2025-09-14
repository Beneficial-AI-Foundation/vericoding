// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed function signatures to resolve compilation errors by using proper postconditions instead of 'result' */
function Sorted(s: seq<int>): bool {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function Merge(s: seq<int>, t: seq<int>): (r: seq<int>)
  requires Sorted(s) && Sorted(t)
  ensures Sorted(r)
  ensures multiset(r) == multiset(s) + multiset(t)
{
  if s == [] then t
  else if t == [] then s
  else if s[0] <= t[0] then [s[0]] + Merge(s[1..], t)
  else [t[0]] + Merge(s, t[1..])
}

function MergeSortFunction(s: seq<int>): (r: seq<int>)
  ensures |r| == |s|
  ensures Sorted(r)
  ensures multiset(r) == multiset(s)
{
  if |s| <= 1 then s
  else
    var mid := |s| / 2;
    var left := s[..mid];
    var right := s[mid..];
    Merge(MergeSortFunction(left), MergeSortFunction(right))
}
// </vc-helpers>

// <vc-spec>
method MergeSort(list: seq<int>) returns (result: seq<int>)
    ensures
        |result| == |list| &&
        (forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]) &&
        multiset(result) == multiset(list)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed to call renamed function */
{
  result := MergeSortFunction(list);
}
// </vc-code>
