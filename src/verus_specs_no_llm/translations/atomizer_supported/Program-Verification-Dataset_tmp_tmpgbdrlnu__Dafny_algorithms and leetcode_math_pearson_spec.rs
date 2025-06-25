// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn isOdd(x: nat) -> bool {
    x % 2 == 1
}

spec fn isEven(x: nat) -> bool {
    x % 2 == 0
}

}