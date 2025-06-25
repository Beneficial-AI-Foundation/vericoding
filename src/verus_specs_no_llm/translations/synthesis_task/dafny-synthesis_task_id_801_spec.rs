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

fn CountEqualNumbers(a: int, b: int, c: int) -> (count: int)
    ensures
        count >= 0 && count <= 3,
        (count == 3) <==> (a == b && b == c),
        (count == 2) <==> ((a == b && b != c) | (a != b && b == c) .len()| (a == c && b != c)),
        (count == 1) <==> (a != b && b != c && a != c)
{
    return 0;
}

}