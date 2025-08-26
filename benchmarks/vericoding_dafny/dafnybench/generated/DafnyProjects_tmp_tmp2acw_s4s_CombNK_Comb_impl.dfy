/* 
* Formal specification and verification of a dynamic programming algorithm for calculating C(n, k).
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial recursive definition of C(n, k), based on the Pascal equality.
// <vc-spec>
function comb(n: nat, k: nat): nat 
  requires 0 <= k <= n
{
  if k == 0 || k == n then 1 else comb(n-1, k) + comb(n-1, k-1)  
}

// <vc-helpers>
// </vc-helpers>

method Comb(n: nat, k: nat) returns (res: nat)
  requires 0 <= k <= n
  ensures res == comb(n, k)
// </vc-spec>
// <vc-code>
{
  // Create a 2D array for dynamic programming
  var dp := new nat[n+1, k+1];
  
  // Fill the base cases and build up using Pascal's triangle
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall row :: 0 <= row < i ==> 
      (forall col :: 0 <= col <= k && col <= row ==> 
        dp[row, col] == comb(row, col))
  {
    var j := 0;
    while j <= k && j <= i
      invariant 0 <= j <= k + 1 && j <= i + 1
      invariant forall row :: 0 <= row < i ==> 
        (forall col :: 0 <= col <= k && col <= row ==> 
          dp[row, col] == comb(row, col))
      invariant forall col :: 0 <= col < j && col <= i ==> 
        dp[i, col] == comb(i, col)
    {
      if j == 0 || j == i {
        dp[i, j] := 1;
      } else {
        dp[i, j] := dp[i-1, j] + dp[i-1, j-1];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  res := dp[n, k];
}
// </vc-code>

lemma combProps(n: nat, k: nat)
   requires 0 <= k <= n
   ensures comb(n, k) == comb(n, n-k)
{
  assume false;
}