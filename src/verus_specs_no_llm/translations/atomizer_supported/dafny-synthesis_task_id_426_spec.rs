// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsOdd(n: int) -> bool {
    n % 2 != 0
}

}