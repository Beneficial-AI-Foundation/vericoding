// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Same helpers, no changes needed */
/* helper modified by LLM (iteration 4): Insert function to insert x into sorted seq */
function Insert(arr: seq<int>, x: int): seq<int>
  decreases |arr|
{
  if |arr| == 0 then [x]
  else if x <= arr[0] then [x] + arr
  else [arr[0]] + Insert(arr[1..], x)
}
/* helper modified by LLM (iteration 4): Recursive sorting function */
function Sort(a: seq<int>): seq<int>
  decreases |a|
  ensures multiset(a) == multiset(result)
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
{
  if |a| < 2 then a
  else Insert(Sort(a[1..]), a[0])
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
/* code modified by LLM (iteration 5): Renamed local sorted to result to avoid duplicate with return name */
{
  var tosort: seq<int> := [];
  for i := 0 to |s| - 1 {
    if p[i] {
      tosort := tosort + [s[i]];
    }
  }
  var sorted_tosort := Sort(tosort);
  var result: seq<int> := [];
  var pos := 0;
  for i := 0 to |s| - 1 {
    if !p[i] {
      result := result + [s[i]];
    } else {
      result := result + [sorted_tosort[pos]];
      pos := pos + 1;
    }
  }
  sorted := result;
}
// </vc-code>
