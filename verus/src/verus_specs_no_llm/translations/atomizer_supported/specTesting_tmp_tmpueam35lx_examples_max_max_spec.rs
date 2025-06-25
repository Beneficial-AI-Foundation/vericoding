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

spec fn post_max(a: int, b: int, m: int) -> bool {
    && m >= a
    && m >= b
    && (m == a || m == b)
}

}