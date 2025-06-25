// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn AtLeastTwiceAsBigPredicate(a: int, b: int) -> bool {
    a >= 2*b
}

}