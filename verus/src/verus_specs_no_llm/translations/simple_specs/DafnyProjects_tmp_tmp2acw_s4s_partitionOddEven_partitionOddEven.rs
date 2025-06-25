// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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