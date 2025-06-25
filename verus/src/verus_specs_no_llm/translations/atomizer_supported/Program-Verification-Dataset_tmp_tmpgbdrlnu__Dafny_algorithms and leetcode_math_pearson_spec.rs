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

spec fn isOdd(x: nat) -> bool {
    x % 2 == 1
}
spec fn isEven(x: nat) -> bool {
    x % 2 == 0
}

}