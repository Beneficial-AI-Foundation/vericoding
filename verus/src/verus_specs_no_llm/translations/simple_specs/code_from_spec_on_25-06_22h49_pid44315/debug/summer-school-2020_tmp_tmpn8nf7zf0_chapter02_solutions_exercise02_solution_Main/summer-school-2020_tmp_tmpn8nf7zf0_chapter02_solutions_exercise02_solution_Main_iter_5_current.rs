use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn divides(f: nat, i: nat) -> bool
    requires 1 <= f
{
    exists|k: nat| i == f * k
}

spec fn IsPrime(i: nat) -> bool {
    && 1 < i
    && (forall|f: nat| (1 < f && f < i) ==> !divides(f, i))
}

}