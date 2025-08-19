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
 var maxj := n - k;
 var c := new nat[1 + maxj];
 forall i | 0 <= i <= maxj {
    c[i] := 1;
 }
 var i := 1;
 /* code modified by LLM (iteration 2): Fixed outer loop invariant with correct base case */
 while i <= k 
 invariant 1 <= i <= k + 1
 invariant forall j :: 0 <= j <= maxj ==> c[j] == comb(n - i + 1, j)
 {
  /* code modified by LLM (iteration 2): Added assertion to help prove inner loop invariants */
  assert forall j :: 0 <= j <= maxj ==> c[j] == comb(n - i + 1, j);
  
  var j := maxj;
  /* code modified by LLM (iteration 2): Fixed inner loop invariants with proper bounds and Pascal's identity reasoning */
  while j >= 1
  invariant 0 <= j <= maxj
  invariant forall l :: 0 <= l < j ==> c[l] == comb(n - i, l)
  invariant forall l :: j <= l <= maxj ==> c[l] == comb(n - i + 1, l)
  {
   /* code modified by LLM (iteration 2): Added assertion to establish Pascal's identity before update */
   assert c[j] == comb(n - i + 1, j);
   assert c[j-1] == comb(n - i + 1, j - 1);
   assert comb(n - i, j) == comb(n - i + 1, j) + comb(n - i + 1, j - 1);
   
   c[j] := c[j] + c[j-1];
   j := j - 1;
  }
  
  /* code modified by LLM (iteration 2): Added assertion to establish outer loop invariant after inner loop */
  assert forall j :: 0 <= j <= maxj ==> c[j] == comb(n - i, j);
  
  i := i + 1;
 }
 
 /* code modified by LLM (iteration 2): Added assertion to prove postcondition */
 assert i == k + 1;
 assert forall j :: 0 <= j <= maxj ==> c[j] == comb(n - i + 1, j);
 assert c[maxj] == comb(n - k - 1 + 1, maxj);
 assert c[maxj] == comb(n - k, n - k);
 assert comb(n - k, n - k) == comb(n, k); // symmetry property
 
 return c[maxj];
}

//IMPL 

method Main()
{
 // Statically checked (proved) test cases!  

 var res1 := comb(40, 10);
 print "combDyn(40, 10) = ", res1, "\n";
}