/* 
* Formal specification and verification of a dynamic programming algorithm for calculating C(n, k).
* FEUP, MIEIC, MFES, 2020/21.
*/

//ATOM 
// Initial recursive definition of C(n, k), based on the Pascal equality.
function comb(n: nat, k: nat): nat 
  requires 0 <= k <= n
{
  if k == 0 || k == n then 1 else comb(n-1, k) + comb(n-1, k-1)  
}
by method
// Calculates C(n,k) iteratively in time O(k*(n-k)) and space O(n-k), 
// with dynamic programming.
{
  /* code modified by LLM (iteration 4): Fixed termination cases and return statements */
  if k == 0 || k == n {
    return 1;
  }
  
  // Use the smaller of k and n-k for efficiency
  var actualK := if k <= n - k then k else n - k;
  
  /* code modified by LLM (iteration 4): Fixed array allocation and initialization */
  var c := new nat[actualK + 1];
  var idx := 0;
  while idx <= actualK 
    invariant 0 <= idx <= actualK + 1
    invariant c.Length == actualK + 1
  {
    c[idx] := 1;
    idx := idx + 1;
  }
  
  /* code modified by LLM (iteration 4): Fixed DP algorithm with proper bounds and invariants */
  var row := 1;
  while row <= n - actualK
    invariant 1 <= row <= n - actualK + 1
    invariant c.Length == actualK + 1
    invariant actualK >= 0
    invariant actualK <= n
    invariant forall i :: 0 <= i < c.Length ==> c[i] >= 1
  {
    var j := actualK;
    while j >= 1
      invariant 0 <= j <= actualK
      invariant c.Length == actualK + 1
      invariant actualK < c.Length
      invariant forall i :: 0 <= i < c.Length ==> c[i] >= 1
    {
      /* code modified by LLM (iteration 4): Added bounds check and overflow prevention */
      assert 0 <= j < c.Length;
      assert 0 <= j-1 < c.Length;
      var oldVal := c[j];
      c[j] := c[j] + c[j-1];
      assert c[j] >= oldVal;
      j := j - 1;
    }
    row := row + 1;
  }
  
  /* code modified by LLM (iteration 4): Added bounds check before return */
  assert 0 <= actualK < c.Length;
  return c[actualK];
}

//IMPL Main
method Main()
{
  /* code modified by LLM (iteration 4): Added proper test with valid preconditions */
  var result := comb(5, 2);
  print "C(5,2) = ", result, "\n";
  
  /* code modified by LLM (iteration 4): Added additional test cases */
  var result2 := comb(4, 0);
  print "C(4,0) = ", result2, "\n";
  
  var result3 := comb(6, 6);
  print "C(6,6) = ", result3, "\n";
}