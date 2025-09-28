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
  var balance := 0;
  var i := 0;
  result := false;
  
  while i < |operations|
    invariant 0 <= i <= |operations|
    invariant balance == sum_prefix(operations, i)
    invariant result <==> (exists j :: 0 < j <= i && sum_prefix(operations, j) < 0)
  {
    balance := balance + operations[i];
    i := i + 1;
    if balance < 0 {
      result := true;
    }
  }
}
// </vc-code>
