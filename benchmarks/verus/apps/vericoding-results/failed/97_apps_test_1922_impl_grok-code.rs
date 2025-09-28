// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
    n >= 1 && m >= 1
}

spec fn count_face_down_cards(n: int, m: int) -> int
    recommends valid_input(n, m)
{
    if n == 1 && m == 1 {
        1
    } else if n == 1 {
        m - 2
    } else if m == 1 {
        n - 2
    } else {
        (n - 2) * (m - 2)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int),
    ensures 
        result as int == count_face_down_cards(n as int, m as int),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    let result: i8;
    if n == 1 && m == 1 {
        result = 1;
    } else if n == 1 {
        result = m - 2;
    } else if m == 1 {
        result = n - 2;
    } else {
        result = (n - 2) * (m - 2);
    }
    result
}
// </vc-code>


}

fn main() {}