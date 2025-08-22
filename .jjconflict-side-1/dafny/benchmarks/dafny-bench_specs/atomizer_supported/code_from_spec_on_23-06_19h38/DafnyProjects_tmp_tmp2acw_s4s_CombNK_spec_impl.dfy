/* 
* Formal specification and verification of a dynamic programming algorithm for calculating C(n, k).
* FEUP, MIEIC, MFES, 2020/21.
*/

// ATOM comb
// Initial recursive definition of C(n, k), based on the Pascal equality.
function comb(n: nat, k: nat): nat 
  requires 0 <= k <= n
{
  if k == 0 || k == n then 1 else comb(n-1, k) + comb(n-1, k-1)  
}

// IMPL combMethod
// Calculates C(n,k) iteratively in time O(k*(n-k)) and space O(n-k), 
// with dynamic programming.
method combMethod(n: nat, k: nat) returns (result: nat)
  requires 0 <= k <= n
  ensures result == comb(n, k)
{
  var maxj := n - k;
  var c := new nat[1 + maxj];
  
  /* code modified by LLM (iteration 4): initialize array with proper loop invariant */
  var idx := 0;
  while idx <= maxj
    invariant 0 <= idx <= maxj + 1
    invariant forall i | 0 <= i < idx :: c[i] == 1
  {
    c[idx] := 1;
    idx := idx + 1;
  }
  
  /* code modified by LLM (iteration 4): corrected outer loop with proper Pascal triangle invariant */
  var i := 1;
  while i <= k 
    invariant 1 <= i <= k + 1
    invariant forall j | 0 <= j <= maxj :: c[j] == comb(n - k + j, i - 1 + j)
  {
    var j := maxj;
    /* code modified by LLM (iteration 4): inner loop with correct Pascal triangle update */
    while j >= 1
      invariant 0 <= j <= maxj
      invariant forall l | j < l <= maxj :: c[l] == comb(n - k + l, i + l)
      invariant forall l | 0 <= l < j :: c[l] == comb(n - k + l, i - 1 + l)
    {
      c[j] := c[j] + c[j-1];
      j := j - 1;
    } 
    i := i + 1;
  }
  
  result := c[maxj];
}

// ATOM combProps
lemma combProps(n: nat, k: nat)
   requires 0 <= k <= n
   ensures comb(n, k) == comb(n, n-k)
{}

// IMPL Main
method Main()
{
  print "Computing some combinations:\n";
  /* code modified by LLM (iteration 4): use method implementation */
  var c1 := combMethod(5, 2);
  print "C(5,2) = ", c1, "\n";
  var c2 := combMethod(10, 3);
  print "C(10,3) = ", c2, "\n";
}

// IMPL testComb
method testComb() {
  /* code modified by LLM (iteration 4): use method implementation for testing */
  var c1 := combMethod(5, 2);
  assert c1 == 10;
  var c2 := combMethod(10, 3);
  assert c2 == 120;
  var c3 := combMethod(4, 0);
  assert c3 == 1;
  var c4 := combMethod(4, 4);
  assert c4 == 1;
  combProps(5, 2);
  var c5 := combMethod(5, 3);
  assert c1 == c5;
}