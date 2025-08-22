//ATOM
function sum(s: seq<int>, n: nat): int
  requires n <= |s|
{
  if |s| == 0 || n == 0 then
    0
  else
    s[0] + sum(s[1..], n-1)
}

//IMPL below_zero
method below_zero(ops: seq<int>) returns (result: bool)
  ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
  var i := 0;
  var current_sum := 0;
  
  /* code modified by LLM (iteration 3): Simplified invariants and fixed logic */
  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant current_sum == sum(ops, i)
    invariant forall k :: 0 <= k < i ==> sum(ops, k) >= 0
  {
    current_sum := current_sum + ops[i];
    i := i + 1;
    
    /* code modified by LLM (iteration 3): Check for negative sum after updating both sum and index */
    if current_sum < 0 {
      /* code modified by LLM (iteration 3): Assert that we found a negative sum at position i */
      assert sum(ops, i) < 0;
      result := true;
      return;
    }
  }
  
  /* code modified by LLM (iteration 3): Assert all prefix sums are non-negative */
  assert forall k :: 0 <= k <= |ops| ==> sum(ops, k) >= 0;
  result := false;
}