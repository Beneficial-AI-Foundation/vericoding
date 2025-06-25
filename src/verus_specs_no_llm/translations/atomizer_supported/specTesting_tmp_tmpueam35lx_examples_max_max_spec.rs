// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn post_max(a: int, b: int, m: int) -> bool {
    and m >= a
    and m >= b
    and (m == a or m == b)
}

}