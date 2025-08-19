//ATOM
function sum(s: seq<int>, n: nat): int
  requires n <= |s|
{
  if |s| == 0 || n == 0 then
    0
  else
    s[0] + sum(s[1..], n-1)
}

//IMPL 
method below_zero(ops: seq<int>) returns (result: bool)
  ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
  result := false;
  var i := 0;
  
  /* code modified by LLM (iteration 3): Fixed loop condition to iterate through valid positions 0 to |ops| inclusive */
  while i <= |ops|
    /* code modified by LLM (iteration 3): Corrected invariant bounds to match loop condition */
    invariant 0 <= i <= |ops| + 1
    /* code modified by LLM (iteration 3): Updated invariant to properly track that we've checked positions 0 to i-1 */
    invariant result <==> exists n: nat :: n < i && n <= |ops| && sum(ops, n) < 0
    /* code modified by LLM (iteration 3): Added invariant for when result is false - all checked positions have non-negative sum */
    invariant !result ==> forall n: nat :: n < i && n <= |ops| ==> sum(ops, n) >= 0
  {
    /* code modified by LLM (iteration 3): Check sum at position i before incrementing */
    if sum(ops, i) < 0 {
      result := true;
      return;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 3): When loop completes, i == |ops| + 1, so we've checked all positions 0 to |ops| */
  assert i == |ops| + 1;
  /* code modified by LLM (iteration 3): All positions have non-negative sum, so result should be false */
  assert forall n: nat :: n <= |ops| ==> sum(ops, n) >= 0;
}