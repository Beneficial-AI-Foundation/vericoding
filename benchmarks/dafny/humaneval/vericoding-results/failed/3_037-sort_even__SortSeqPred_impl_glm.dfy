// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 5): fixed range in sequence comprehension from 0..|s| to 0..|s|-1 */
  var toSort: seq<int> := [ s[i] | i in 0..|s| - 1 if p[i] ];
  var arr := toSort;
  for i := 0 to |arr|
  {
    var minIndex := i;
    for j := i+1 to |arr|
    {
      if arr[j] < arr[minIndex] {
        minIndex := j;
      }
    }
    var temp := arr[i];
    arr := arr[i := arr[minIndex]];
    arr := arr[minIndex := temp];
  }
  var result := s;
  var k := 0;
  for i := 0 to |s|
  {
    if p[i] {
      result := result[i := arr[k]];
      k := k + 1;
    }
  }
  return result;
}
// </vc-code>
