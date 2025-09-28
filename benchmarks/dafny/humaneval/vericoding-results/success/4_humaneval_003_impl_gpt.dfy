// <vc-preamble>

function sum_prefix(ops: seq<int>, len: nat): int
  requires len <= |ops|
{
  if len == 0 then 0
  else sum_prefix(ops, len-1) + ops[len-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate summarizing whether a negative prefix exists up to k */
function existsNegPrefixUpTo(ops: seq<int>, k: nat): bool
  requires k <= |ops|
{
  exists i :: 0 < i <= k && sum_prefix(ops, i) < 0
}
// </vc-helpers>

// <vc-spec>
method below_zero(operations: seq<int>) returns (result: bool)
  ensures result <==> (exists i :: 0 < i <= |operations| && sum_prefix(operations, i) < 0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): scan prefix sums and track if any negative prefix sum occurs */
  var n := |operations|;
  var i: nat := 0;
  var sum: int := 0;
  var found: bool := false;
  while i < n
    invariant 0 <= i <= n
    invariant sum == sum_prefix(operations, i)
    invariant found <==> (exists j :: 0 < j <= i && sum_prefix(operations, j) < 0)
  {
    sum := sum + operations[i];
    i := i + 1;
    if sum < 0 {
      found := true;
    }
  }
  result := found;
}
// </vc-code>
