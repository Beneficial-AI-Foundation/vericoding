// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CountEqualNumbers(a: int, b: int, c: int) -> (count: int)
    ensures count >= 0 and count <= 3,
            (count == 3) <==> (a == b and b == c),
            (count == 2) <==> ((a == b and b != c) | (a != b and b == c) .len()| (a == c and b != c)),
            (count == 1) <==> (a != b and b != c and a != c)
{
}

}