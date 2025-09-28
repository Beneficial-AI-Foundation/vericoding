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
  /* code modified by LLM (iteration 5): fixed postcondition by ensuring both directions of biconditional */
  var i := 1;
  while i <= |operations|
    invariant 1 <= i <= |operations| + 1
    invariant forall j :: 0 < j < i ==> sum_prefix(operations, j) >= 0
  {
    if sum_prefix(operations, i) < 0 {
      result := true;
      assert sum_prefix(operations, i) < 0;
      assert exists k :: 0 < k <= |operations| && sum_prefix(operations, k) < 0;
      return;
    }
    i := i + 1;
  }
  result := false;
  assert forall j :: 0 < j <= |operations| ==> sum_prefix(operations, j) >= 0;
  assert !(exists k :: 0 < k <= |operations| && sum_prefix(operations, k) < 0);
}
// </vc-code>
