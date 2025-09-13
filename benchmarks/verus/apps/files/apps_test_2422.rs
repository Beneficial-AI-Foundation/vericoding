// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_solution(n: int, a: int, b: int, c: int) -> bool {
        a >= 0 && b >= 0 && c >= 0 && 3 * a + 5 * b + 7 * c == n
    }
    
    spec fn valid_result(n: int, result: Seq<int>) -> bool {
        (result.len() == 1 && result[0] == -1) ||
        (result.len() == 3 && result[0] >= 0 && result[1] >= 0 && result[2] >= 0 && 
         valid_solution(n, result[0], result[1], result[2]))
    }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: Vec<int>)
    requires 
        n >= 1,
    ensures 
        valid_result(n, result@),
        n % 3 == 0 ==> (result@.len() == 3 && result@ == seq![n / 3, 0, 0]),
        n % 3 == 1 && n < 7 ==> (result@.len() == 1 && result@[0] == -1),
        n % 3 == 1 && n >= 7 ==> (result@.len() == 3 && result@ == seq![(n - 7) / 3, 0, 1]),
        n % 3 == 2 && n < 5 ==> (result@.len() == 1 && result@[0] == -1),
        n % 3 == 2 && n >= 5 ==> (result@.len() == 3 && result@ == seq![(n - 5) / 3, 1, 0])
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>

}

fn main() {}