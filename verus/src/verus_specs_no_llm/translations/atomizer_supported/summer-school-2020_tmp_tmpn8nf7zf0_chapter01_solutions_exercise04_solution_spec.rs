// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn AtLeastTwiceAsBigPredicate(a: int, b: int) -> bool {
    a >= 2*b
}

}