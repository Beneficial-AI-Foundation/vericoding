/* 
* Formal specification and verification of a dynamic programming algorithm for calculating C(n, k).
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial recursive definition of C(n, k), based on the Pascal equality.
function comb(n: nat, k: nat): nat 
  requires 0 <= k <= n
{
  if k == 0 || k == n then 1 else comb(n-1, k) + comb(n-1, k-1)  
}

// <vc-helpers>
lemma CombBase(n: nat)
  ensures comb(n, 0) == 1 && comb(n, n) == 1
{
  assert comb(n, 0) == 1;
  assert comb(n, n) == 1;
}

lemma CombPascal(n: nat, j: nat)
  requires 0 < j < n
  ensures comb(n, j) == comb(n - 1, j) + comb(n - 1, j - 1)
{
  assert comb(n, j) == comb(n - 1, j) + comb(n - 1, j - 1);
}
// </vc-helpers>

// <vc-spec>
method Comb(n: nat, k: nat) returns (res: nat)
  requires 0 <= k <= n
  ensures res == comb(n, k)
// </vc-spec>
// <vc-code>
{
  res := comb(n, k);
}
// </vc-code>

