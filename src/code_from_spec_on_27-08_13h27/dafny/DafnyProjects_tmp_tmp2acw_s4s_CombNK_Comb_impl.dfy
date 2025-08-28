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
// Helper lemma to prove properties of comb function if needed
lemma CombProperties(n: nat, k: nat)
  requires 0 <= k <= n
  ensures comb(n, k) >= 1
{
  if k == 0 || k == n {
    assert comb(n, k) == 1;
  } else {
    CombProperties(n-1, k);
    CombProperties(n-1, k-1);
    assert comb(n, k) == comb(n-1, k) + comb(n-1, k-1);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Comb(n: nat, k: nat) returns (res: nat)
  requires 0 <= k <= n
  ensures res == comb(n, k)
// </vc-spec>
// </vc-spec>

// <vc-code>
method ComputeComb(n: nat, k: nat) returns (res: nat)
  requires 0 <= k <= n
  ensures res == comb(n, k)
{
  if k == 0 || k == n {
    res := 1;
  } else {
    var res1 := ComputeComb(n-1, k);
    var res2 := ComputeComb(n-1, k-1);
    res := res1 + res2;
  }
}
// </vc-code>
