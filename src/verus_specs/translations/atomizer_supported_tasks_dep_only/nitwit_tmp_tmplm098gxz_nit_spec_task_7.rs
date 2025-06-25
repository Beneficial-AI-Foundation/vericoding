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

}