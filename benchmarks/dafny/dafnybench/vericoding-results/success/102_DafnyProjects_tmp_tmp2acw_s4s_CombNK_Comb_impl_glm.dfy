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
lemma comb_pascal(n: nat, k: nat)
  requires 1 <= k < n
  ensures comb(n, k) == comb(n-1, k) + comb(n-1, k-1)
{
  // Since 1<=k<n, the condition k==0||k==n is false
  assert !(k == 0 || k == n);
  calc {
    comb(n, k);
    == { }  // Function body expansion with false condition
    comb(n-1, k) + comb(n-1, k-1);
  }
}

lemma comb_base(n: nat, k: nat)
  requires k == 0 || k == n
  ensures comb(n, k) == 1
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
    return 1;
  }
  var left := Comb(n-1, k);
  var right := Comb(n-1, k-1);
  assert 1 <= k < n;
  comb_pascal(n, k);
  return left + right;
}
// </vc-code>

