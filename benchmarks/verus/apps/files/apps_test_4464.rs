// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(a: int, b: int, c: int) -> bool {
        1 <= a <= 100 && 1 <= b <= 100 && 0 <= c < b
    }
    
    spec fn is_solvable(a: int, b: int, c: int) -> bool {
        exists|i: int| 1 <= i < b && (i * (a % b)) % b == c
    }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, c: int) -> (result: String)
    requires 
        valid_input(a, b, c)
    ensures 
        result == "YES" <==> is_solvable(a, b, c),
        result == "NO" || result == "YES"
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>

}

fn main() {}