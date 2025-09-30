// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed syntax by removing 'method' keyword */
function Swap(s: seq<int>, i: int, j: int): seq<int>
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures |Swap(s, i, j)| == |s|
  ensures Swap(s, i, j)[i] == s[j]
  ensures Swap(s, i, j)[j] == s[i]
  ensures forall k :: 0 <= k < |s| && k != i && k != j ==> Swap(s, i, j)[k] == s[k]
  ensures multiset(s) == multiset(Swap(s, i, j))
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
  /* code modified by LLM (iteration 3): Fixed syntax error in helper function */
  sorted := s;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
    invariant forall x, y :: 0 <= x < y < i && p[x] && p[y] ==> sorted[x] <= sorted[y]
    invariant forall x, y :: 0 <= x < i && i <= y < |s| && p[x] && p[y] ==> sorted[x] <= sorted[y]
  {
    if p[i] {
      var minIdx := i;
      var j := i + 1;
      while j < |s|
        invariant i < j <= |s|
        invariant i <= minIdx < |s|
        invariant p[minIdx]
        invariant forall k :: i <= k < j && p[k] ==> sorted[minIdx] <= sorted[k]
      {
        if p[j] && sorted[j] < sorted[minIdx] {
          minIdx := j;
        }
        j := j + 1;
      }
      if minIdx != i {
        sorted := Swap(sorted, i, minIdx);
      }
    }
    i := i + 1;
  }
}
// </vc-code>
