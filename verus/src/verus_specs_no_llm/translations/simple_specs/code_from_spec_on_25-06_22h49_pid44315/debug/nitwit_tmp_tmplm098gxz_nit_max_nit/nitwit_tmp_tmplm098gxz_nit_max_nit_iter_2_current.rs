use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nitness(b: nat, n: nat) -> bool 
    requires valid_base(b)
{
    0 <= n < b
}

spec fn is_max_nit(b: nat, q: nat) -> bool {
    q == b - 1
}

spec fn valid_base(b: nat) -> bool {
    b >= 2
}

fn max_nit(b: nat) -> (nmax: nat)
    requires
        valid_base(b)
    ensures
        nitness(b, nmax),
        is_max_nit(b, nmax)
{
    assert(b >= 2);
    assert(b - 1 >= 1);
    assert(b - 1 < b);
    (b - 1) as nat
}

}