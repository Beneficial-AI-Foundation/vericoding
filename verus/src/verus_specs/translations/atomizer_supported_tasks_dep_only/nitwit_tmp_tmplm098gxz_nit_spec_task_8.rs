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

pub fn nit_flip(b: nat, n: nat) -> (nf: nat)
    requires(valid_base(b))
    requires(nitness(b, n))
    ensures(nitness(b, nf))
{
}

spec fn bibble(b: nat, a: Seq<nat>) -> bool {
    valid_base(b) && 
    a.len() == 4 && 
    forall|n: nat| a.contains(n) ==> nitness(b, n)
}

pub fn bibble_flip(b: nat, p: Seq<nat>) -> (fp: Seq<nat>)
    requires(valid_base(b))
    requires(bibble(b, p))
    ensures(bibble(b, fp))
{
}

}