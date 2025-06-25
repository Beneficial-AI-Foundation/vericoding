use vstd::prelude::*;

verus! {

// Initial recursive definition of C(n, k), based on the Pascal equality.
spec fn comb(n: nat, k: nat) -> nat
    recommends 0 <= k <= n
{
    if k == 0 || k == n { 1 } else { comb((n-1) as nat, k) + comb((n-1) as nat, (k-1) as nat) }
}

// Calculates C(n,k) iteratively in time O(k*(n-k)) and space O(n-k), 
// with dynamic programming.
pub fn comb_method(n: nat, k: nat) -> (result: nat)
    requires 0 <= k <= n
    ensures result == comb(n, k)
{
    unimplemented!()
}

pub fn main() {
}

}