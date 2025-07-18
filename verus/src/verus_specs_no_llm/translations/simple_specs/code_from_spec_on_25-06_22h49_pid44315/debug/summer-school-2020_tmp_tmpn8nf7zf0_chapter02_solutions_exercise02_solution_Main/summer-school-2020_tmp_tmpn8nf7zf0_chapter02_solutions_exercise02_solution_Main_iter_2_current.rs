use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn divides(f: nat, i: nat) -> bool
    requires 1 <= f
{
    i % f == 0
}

spec fn IsPrime(i: nat) -> bool {
    && 1 < i
    && (forall|f: nat| 1 < f < i ==> !divides(f, i))
}

}