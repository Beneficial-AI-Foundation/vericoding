// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nitness(b: nat, n: nat)
 requires (valid_base(b)) -> bool {
    0 <= n < b
}
spec fn valid_base(b: nat) -> bool {
    b >= 2
}

fn nit_add(b: nat, x: nat, y: nat) -> (z: nat, carry: nat)
    requires
        (valid_base(b)),
        (nitness(b, x)),
        (nitness(b, y))
    ensures
        (nitness(b, z)),
        (nitness(b, carry))
 // This is a useful fact for doing general form addition.,
        (carry == 0 || carry == 1)
{
    return (0, 0);
}

}