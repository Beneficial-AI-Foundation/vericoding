// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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