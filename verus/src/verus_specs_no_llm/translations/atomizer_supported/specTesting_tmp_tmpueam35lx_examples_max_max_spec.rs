// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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