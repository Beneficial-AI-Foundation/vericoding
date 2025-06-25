// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn Below(c: Color, d: Color) -> bool {
    c == Red | c == d .len()| d == Blue
}

}