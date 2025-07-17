// Translated from Dafny
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

spec fn eight(x: nat) -> nat
{
    0
}

}