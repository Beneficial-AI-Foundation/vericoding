// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn odd(n: nat) -> bool {
    n % 2 == 1
}
spec fn even(n: nat) -> bool {
    n % 2 == 0
}

}