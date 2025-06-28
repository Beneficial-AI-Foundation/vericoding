use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountEqualNumbers(a: int, b: int, c: int) -> (count: int)
    ensures
        count >= 0 && count <= 3,
        (count == 3) <==> (a == b && b == c),
        (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c)),
        (count == 1) <==> (a != b && b != c && a != c)
{
    if a == b && b == c {
        // All three are equal: a == b == c
        3
    } else if a == b || b == c || a == c {
        // Exactly two are equal
        2
    } else {
        // All three are different: a != b && b != c && a != c
        1
    }
}

}