// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added decreases clause to fix termination errors */
function findMinIndex(arr: seq<int>, start: int, end: int): int
  requires 0 <= start < end <= |arr|
  ensures start <= findMinIndex(arr, start, end) < end
  ensures forall k :: start <= k < end ==> arr[findMinIndex(arr, start, end)] <= arr[k]
  decreases end - start
{
  if start + 1 == end then start
  else if arr[start] <= arr[findMinIndex(arr, start + 1, end)] then start
  else findMinIndex(arr, start + 1, end)
}

function findMaxIndex(arr: seq<int>, start: int, end: int): int
  requires 0 <= start < end <= |arr|
  ensures start <= findMaxIndex(arr, start, end) < end
  ensures forall k :: start <= k < end ==> arr[findMaxIndex(arr, start, end)] >= arr[k]
  decreases end - start
{
  if start + 1 == end then start
  else if arr[start] >= arr[findMaxIndex(arr, start + 1, end)] then start
  else findMaxIndex(arr, start + 1, end)
}
// </vc-helpers>

// <vc-spec>
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)

    ensures |s| == |strange|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): same implementation with fixed helper functions */
  if |s| == 0 {
    strange := [];
    return;
  }
  
  var remaining := s;
  strange := [];
  
  while |remaining| > 0
    invariant |s| == |strange| + |remaining|
    decreases |remaining|
  {
    var minIdx := findMinIndex(remaining, 0, |remaining|);
    var maxIdx := findMaxIndex(remaining, 0, |remaining|);
    
    if |strange| % 2 == 0 {
      strange := strange + [remaining[minIdx]];
      remaining := remaining[..minIdx] + remaining[minIdx+1..];
    } else {
      strange := strange + [remaining[maxIdx]];
      remaining := remaining[..maxIdx] + remaining[maxIdx+1..];
    }
  }
}
// </vc-code>
