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

pub fn nit_increment(b: nat, n: nat) -> (sum: nat, carry: nat)
    requires(valid_base(b))
    requires(nitness(b, n))
    ensures(nitness(b, sum))
    ensures(nitness(b, carry))
{
}

}