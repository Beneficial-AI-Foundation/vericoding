// <vc-preamble>

function sum_prefix(ops: seq<int>, len: nat): int
  requires len <= |ops|
{
  if len == 0 then 0
  else sum_prefix(ops, len-1) + ops[len-1]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method below_zero(operations: seq<int>) returns (result: bool)
  ensures result <==> (exists i :: 0 < i <= |operations| && sum_prefix(operations, i) < 0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): restructured loop with flag to track negative prefix */
  var n := |operations|;
  var i := 1;
  var sum := 0;
  var found := false;

  while i <= n
    invariant 1 <= i <= n + 1
    invariant sum == sum_prefix(operations, i-1)
    invariant !found ==> (forall j: int :: 1 <= j < i ==> sum_prefix(operations, j) >= 0)
    invariant found ==> (exists j: int :: 1 <= j < i && sum_prefix(operations, j) < 0)
  {
    sum := sum + operations[i-1];
    if sum < 0 {
      found := true;
    }
    i := i + 1;
  }

  return found;
}
// </vc-code>
