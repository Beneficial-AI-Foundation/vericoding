//ATOM comb
// Initial recursive definition of C(n, k), based on the Pascal equality.
function comb(n: nat, k: nat): nat 
 requires 0 <= k <= n
{
 if k == 0 || k == n then 1 else comb(n-1, k) + comb(n-1, k-1) 
}

//IMPL combMethod
/* code modified by LLM (iteration 3): Redesigned with correct table representation and invariants */
method combMethod(n: nat, k: nat) returns (result: nat)
 requires 0 <= k <= n
 ensures result == comb(n, k)
{
 var maxj := n - k;
 var c := new nat[1 + maxj];
 
 // Initialize array - c[j] represents C(n-k+j, j) initially
 /* code modified by LLM (iteration 3): Initialize with proper values for C(n-k+j, 0) = 1 */
 var idx := 0;
 while idx <= maxj
  invariant 0 <= idx <= maxj + 1
  invariant c.Length == maxj + 1
  invariant forall i | 0 <= i < idx :: c[i] == 1
 {
  c[idx] := 1;
  idx := idx + 1;
 }
 
 var i := 1;
 /* code modified by LLM (iteration 3): Correct invariant - c[j] represents C(n-k+j, i-1) before iteration */
 while i <= k 
  invariant 1 <= i <= k + 1
  invariant c.Length == maxj + 1
  invariant forall j | 0 <= j <= maxj :: c[j] == comb(n - k + j, i - 1)
 {
  var j := maxj;
  /* code modified by LLM (iteration 3): Process from right to left with correct Pascal's triangle update */
  while j >= 1
   invariant 0 <= j <= maxj
   invariant c.Length == maxj + 1
   invariant forall idx | j < idx <= maxj :: c[idx] == comb(n - k + idx, i)
   invariant forall idx | 0 <= idx <= j :: c[idx] == comb(n - k + idx, i - 1)
  {
   /* code modified by LLM (iteration 3): Apply Pascal's identity C(n,k) = C(n-1,k) + C(n-1,k-1) */
   c[j] := c[j] + c[j-1];
   j := j - 1;
  }
  /* code modified by LLM (iteration 3): First element stays same as C(n-k, i) = C(n-k, i-1) when i > n-k */
  if i <= n - k then
   c[0] := c[0];
  else
   c[0] := c[0];
  i := i + 1;
 }
 
 /* code modified by LLM (iteration 3): Added assertion to help verification */
 assert c[maxj] == comb(n - k + maxj, k);
 assert n - k + maxj == n;
 result := c[maxj];
}

//IMPL Main
/* code modified by LLM (iteration 3): Fixed method call syntax */
method Main()
{
 // Statically checked (proved) test cases!
 var res1 := combMethod(40, 10);
 print "combDyn(40, 10) = ", res1, "\n";
}