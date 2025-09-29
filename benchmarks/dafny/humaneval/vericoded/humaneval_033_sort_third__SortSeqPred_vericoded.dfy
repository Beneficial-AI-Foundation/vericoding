// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): swap helper function */
function swap<T>(s: seq<T>, i: int, j: int): seq<T>
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures |swap(s, i, j)| == |s|
  ensures swap(s, i, j)[i] == s[j]
  ensures swap(s, i, j)[j] == s[i]
  ensures forall k :: 0 <= k < |s| && k != i && k != j ==> swap(s, i, j)[k] == s[k]
  ensures multiset(s) == multiset(swap(s, i, j))
{
  s[i := s[j]][j := s[i]]
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
  /* code modified by LLM (iteration 4): bubble sort with proper sorting invariant */
  sorted := s;
  if |s| <= 1 {
    return;
  }
  
  var n := |s|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
    invariant forall x, y :: 0 <= x < i && i <= y < n && p[x] && p[y] ==> sorted[x] <= sorted[y]
    invariant forall x, y :: 0 <= x < y < i && p[x] && p[y] ==> sorted[x] <= sorted[y]
  {
    var j := i + 1;
    while j < n
      invariant i < j <= n
      invariant |sorted| == |s|
      invariant multiset(s) == multiset(sorted)
      invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
      invariant forall x, y :: 0 <= x < i && i <= y < n && p[x] && p[y] ==> sorted[x] <= sorted[y]
      invariant forall x, y :: 0 <= x < y < i && p[x] && p[y] ==> sorted[x] <= sorted[y]
      invariant forall y :: i < y < j && p[i] && p[y] ==> sorted[i] <= sorted[y]
    {
      if p[i] && p[j] && sorted[i] > sorted[j] {
        sorted := swap(sorted, i, j);
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
