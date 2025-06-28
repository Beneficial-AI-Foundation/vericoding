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
        3
    } else if a == b || b == c || a == c {
        2
    } else {
        1
    }
}

}

The implementation:

This satisfies all the postconditions:
- The result is always 1, 2, or 3 (within bounds 0-3)
- Returns 3 exactly when all three are equal
- Returns 2 exactly when exactly two are equal
- Returns 1 exactly when all are different