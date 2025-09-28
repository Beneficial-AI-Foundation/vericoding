// <vc-preamble>

function sum_prefix(ops: seq<int>, len: nat): int
  requires len <= |ops|
{
  if len == 0 then 0
  else sum_prefix(ops, len-1) + ops[len-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): reveals property of sum_prefix for proof */
lemma SumPrefixPlusOne(ops: seq<int>, i: nat)
  requires i < |ops|
  ensures sum_prefix(ops, i + 1) == sum_prefix(ops, i) + ops[i]
{ }
// </vc-helpers>

// <vc-spec>
method below_zero(operations: seq<int>) returns (result: bool)
  ensures result <==> (exists i :: 0 < i <= |operations| && sum_prefix(operations, i) < 0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): call helper lemma to prove postcondition on early return */
  result := false;
  var current_sum := 0;
  var i := 0;
  while i < |operations|
    invariant 0 <= i <= |operations|
    invariant current_sum == sum_prefix(operations, i)
    invariant !result ==> !(exists j :: 0 < j <= i && sum_prefix(operations, j) < 0)
  {
    current_sum := current_sum + operations[i];
    if current_sum < 0 {
      SumPrefixPlusOne(operations, i);
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
