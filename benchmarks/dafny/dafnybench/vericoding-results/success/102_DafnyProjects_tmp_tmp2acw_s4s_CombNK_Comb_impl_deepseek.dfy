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
lemma Lemma_CombIndexing(n: nat, k: nat)
  requires 0 <= k <= n
  ensures 0 <= k <= n && (n == 0 ==> k == 0)
{
}

lemma Lemma_BaseCases(n: nat, k: nat)
  requires 0 <= k <= n
  ensures (k == 0 || k == n) ==> comb(n, k) == 1
{
}

lemma Lemma_RecursiveCase(n: nat, k: nat)
  requires 0 <= k <= n
  requires n > 0 && 0 < k < n
  ensures comb(n, k) == comb(n-1, k) + comb(n-1, k-1)
{
}
// </vc-helpers>

// <vc-spec>
method Comb(n: nat, k: nat) returns (res: nat)
  requires 0 <= k <= n
  ensures res == comb(n, k)
// </vc-spec>
// <vc-code>
{
  if k == 0 || k == n {
    res := 1;
  } else {
    var res1: nat;
    var res2: nat;
    
    res1 := Comb(n-1, k);
    res2 := Comb(n-1, k-1);
    res := res1 + res2;
  }
}
// </vc-code>

