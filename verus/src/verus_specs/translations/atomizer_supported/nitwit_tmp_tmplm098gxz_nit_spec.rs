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

pub fn nit_add(b: nat, x: nat, y: nat) -> (z: nat, carry: nat)
    requires(valid_base(b))
    requires(nitness(b, x))
    requires(nitness(b, y))
    ensures(nitness(b, z))
    ensures(nitness(b, carry))
    ensures(carry == 0 || carry == 1)
{
}

pub fn nit_add_three(b: nat, c: nat, x: nat, y: nat) -> (z: nat, carry: nat)
    requires(valid_base(b))
    requires(c == 0 || c == 1)
    requires(nitness(b, x))
    requires(nitness(b, y))
    ensures(nitness(b, z))
    ensures(nitness(b, carry))
    ensures(carry == 0 || carry == 1)
{
}

spec fn bibble(b: nat, a: Seq<nat>) -> bool {
    valid_base(b) && 
    a.len() == 4 && 
    forall|n: nat| a.contains(n) ==> nitness(b, n)
}

pub fn bibble_add(b: nat, p: Seq<nat>, q: Seq<nat>) -> (r: Seq<nat>)
    requires(valid_base(b))
    requires(bibble(b, p))
    requires(bibble(b, q))
    ensures(bibble(b, r))
{
}

pub fn bibble_increment(b: nat, p: Seq<nat>) -> (r: Seq<nat>)
    requires(valid_base(b))
    requires(bibble(b, p))
    ensures(bibble(b, r))
{
}

pub fn bibble_flip(b: nat, p: Seq<nat>) -> (fp: Seq<nat>)
    requires(valid_base(b))
    requires(bibble(b, p))
    ensures(bibble(b, fp))
{
}

pub fn n_complement(b: nat, p: Seq<nat>) -> (com: Seq<nat>)
    requires(valid_base(b))
    requires(bibble(b, p))
    ensures(bibble(b, com))
{
}

pub fn Main()
{
}

}