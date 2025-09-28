// <vc-preamble>

function sum_prefix(ops: seq<int>, len: nat): int
  requires len <= |ops|
{
  if len == 0 then 0
  else sum_prefix(ops, len-1) + ops[len-1]
}
// </vc-preamble>

// <vc-helpers>
lemma SumPrefix_Unfold(ops: seq<int>, len: nat)
  requires len > 0 && len <= |ops|
  ensures sum_prefix(ops, len) == sum_prefix(ops, len-1) + ops[len-1]
{
  // Unfold the definition of sum_prefix and simplify using len > 0
  assert sum_prefix(ops, len) == if len == 0 then 0 else sum_prefix(ops, len-1) + ops[len-1];
  assert sum_prefix(ops, len) == sum_prefix(ops, len-1) + ops[len-1];
}

// </vc-helpers>

// <vc-spec>
method below_zero(operations: seq<int>) returns (result: bool)
  ensures result <==> (exists i :: 0 < i <= |operations| && sum_prefix(operations, i) < 0)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  var s: int := 0;
  result := false;
  while i < |operations|
    invariant 0 <= i <= |operations|
    invariant s == sum_prefix(operations, i)
    invariant (result <==> exists j :: 0 < j <= i && sum_prefix(operations, j) < 0)
  {
    var op := operations[i];
    s := s + op;
    // s equals sum_prefix(operations, i+1) by definition
    SumPrefix_Unfold(operations, i+1);
    assert s == sum_prefix(operations, i+1);
    i := i + 1;
    if s < 0 {
      result := true;
    }
  }
}
// </vc-code>
