use vstd::prelude::*;

verus! {

spec fn F(x: nat, y: nat) -> nat;

proof fn AboutF(x: nat, y: nat)
    ensures F(x, y) == 13 * x
{
}

spec fn G(x: nat, y: nat) -> nat;

spec fn H(x: int, y: nat) -> int;

spec fn J(x: int) -> int;

spec fn K(x: int, y: nat) -> int;

pub fn Main() {
}

}