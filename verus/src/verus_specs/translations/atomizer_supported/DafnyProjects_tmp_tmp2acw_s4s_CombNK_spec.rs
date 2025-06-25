use vstd::prelude::*;

verus! {

spec fn comb(n: nat, k: nat) -> nat 
    recommends 0 <= k <= n
{
    if k == 0 || k == n { 1 } else { comb((n-1) as nat, k) + comb((n-1) as nat, (k-1) as nat) }
}

pub fn comb_method(n: nat, k: nat) -> (result: nat)
    requires(0 <= k <= n)
    ensures(result == comb(n, k))
{
    // Implementation left empty
}

proof fn combProps(n: nat, k: nat)
    requires(0 <= k <= n)
    ensures(comb(n, k) == comb(n, (n-k) as nat))
{
}

pub fn Main()
{
}

pub fn testComb() 
{
}

}