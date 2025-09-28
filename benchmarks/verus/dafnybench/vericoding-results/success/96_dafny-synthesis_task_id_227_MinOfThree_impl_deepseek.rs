use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn min(a: int, b: int) -> int {
    if a <= b {
        a
    } else {
        b
    }
}

proof fn min_lemma(a: int, b: int, c: int)
    ensures
        min(a, min(b, c)) <= a,
        min(a, min(b, c)) <= b,
        min(a, min(b, c)) <= c,
        min(a, min(b, c)) == a || min(a, min(b, c)) == b || min(a, min(b, c)) == c
{
    reveal(min);
    if a <= b {
        if a <= c {
            assert(min(a, min(b, c)) == a);
        } else {
            assert(min(a, min(b, c)) == c);
        }
    } else {
        if b <= c {
            assert(min(a, min(b, c)) == b);
        } else {
            assert(min(a, min(b, c)) == c);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i32, b: i32, c: i32) -> (min: i32)
    ensures
        min <= a && min <= b && min <= c,
        (min == a) || (min == b) || (min == c),
// </vc-spec>
// <vc-code>
{
    proof {
        min_lemma(a as int, b as int, c as int);
    }
    let min_ab = if a <= b { a } else { b };
    let result = if min_ab <= c { min_ab } else { c };
    result
}
// </vc-code>

fn main() {
}

}