// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Below(c: Color, d: Color) -> bool {
    c == Red | c == d .len()| d == Blue
}

}