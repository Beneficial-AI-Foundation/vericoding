use vstd::prelude::*;

verus! {

spec fn valid_base(b: nat) -> bool {
    b >= 2
}

spec fn nitness(b: nat, n: nat) -> bool
    recommends valid_base(b)
{
    0 <= n < b
}

spec fn is_max_nit(b: nat, q: nat) -> bool {
    q == b - 1
}

pub fn max_nit(b: nat) -> (nmax: nat)
    requires(valid_base(b))
    ensures(nitness(b, nmax))
    ensures(is_max_nit(b, nmax))
{
}

}