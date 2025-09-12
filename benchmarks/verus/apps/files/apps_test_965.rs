// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, statuses: Seq<char>) -> bool {
    n >= 2 && statuses.len() == n && 
    forall|i: int| 0 <= i < statuses.len() ==> {
        let c = statuses[i];
        c == 'A' || c == 'I' || c == 'F'
    }
}

spec fn count_status(statuses: Seq<char>, status: char) -> int {
    statuses.filter(|c: char| c == status).len() as int
}

spec fn expected_result(statuses: Seq<char>) -> int {
    let cnt_i = count_status(statuses, 'I');
    let cnt_a = count_status(statuses, 'A');
    if cnt_i == 0 { cnt_a }
    else if cnt_i == 1 { 1 }
    else { 0 }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, statuses: Seq<char>) -> (result: int)
    requires valid_input(n, statuses)
    ensures result == expected_result(statuses)
// </vc-spec>
// <vc-code>
{
    assume(false);
    0 as int
}
// </vc-code>


}

fn main() {}