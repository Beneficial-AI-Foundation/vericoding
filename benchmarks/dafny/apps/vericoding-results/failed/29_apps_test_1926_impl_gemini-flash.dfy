// <vc-preamble>
predicate ValidInput(n: int, a: seq<int>)
{
  n >= 2 && |a| == n
}

function CountViolationsForK(a: seq<int>, n: int, k: int): int
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
{
  |set i | 2 <= i <= n && 
    var parent_idx := (i + k - 2) / k;
    parent_idx >= 1 && a[i-1] < a[parent_idx-1]|
}

predicate ValidOutput(result: seq<int>, n: int, a: seq<int>)
  requires n >= 2 && |a| == n
{
  |result| == n - 1 &&
  (forall k :: 1 <= k <= n - 1 ==> result[k-1] >= 0) &&
  (forall k :: 1 <= k <= n - 1 ==> result[k-1] == CountViolationsForK(a, n, k))
}
// </vc-preamble>

// <vc-helpers>
function GetParentIndex(i: int, k: int): int
  requires i >= 2 && k >= 1
{
  (i + k - 2) / k
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: seq<int>)
  requires ValidInput(n, a)
  ensures ValidOutput(result, n, a)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed compilation error related to `new int[n-1] as seq<int>` creating a `seq<int>` and removed the cast to fix */
{
  var results_seq: seq<int>;
  if n - 1 > 0 {
    results_seq := new int[n - 1](_ => 0);
  } else {
    results_seq := [];
  }

  for k := 1 to n - 1
    invariant 1 <= k <= n
    invariant |results_seq| == n - 1
    invariant forall kk :: 1 <= kk < k ==> results_seq[kk-1] == CountViolationsForK(a, n, kk)
  {
    var violations := 0;
    for i := 2 to n
      invariant 2 <= i <= n + 1
      invariant violations == |set idx | 2 <= idx < i && var parent_idx := GetParentIndex(idx, k); parent_idx >= 1 && a[idx-1] < a[parent_idx-1]|
    {
      var parent_idx := GetParentIndex(i, k);
      if parent_idx >= 1 && parent_idx <= n && a[i-1] < a[parent_idx-1] {
        violations := violations + 1;
      }
    }
    results_seq := results_seq[0 .. k-1] + [violations] + results_seq[k ..];
  }

  result := results_seq;
}
// </vc-code>
