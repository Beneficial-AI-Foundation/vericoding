// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, statuses: Seq<char>) -> bool {
    n >= 2 && statuses.len() == n && 
    forall|i: int| 0 <= i < statuses.len() ==> (statuses[i] == 'A' || statuses[i] == 'I' || statuses[i] == 'F')
}

spec fn count_status(statuses: Seq<char>, status: char) -> int {
    seq_count(statuses, status)
}

spec fn seq_count(s: Seq<char>, target: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let rest_count = seq_count(s.drop_first(), target);
        if s[0] == target {
            rest_count + 1
        } else {
            rest_count
        }
    }
}

spec fn expected_result(statuses: Seq<char>) -> int {
    let cnt_i = count_status(statuses, 'I');
    let cnt_a = count_status(statuses, 'A');
    if cnt_i == 0 { cnt_a }
    else if cnt_i == 1 { 1 }
    else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed. */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, statuses: Vec<char>) -> (result: i8)
    requires valid_input(n as int, statuses@)
    ensures result as int == expected_result(statuses@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed variables from nat to int to fix type mismatches and casting errors, ensuring compatibility with Verus sequence operations. */
{
    let mut cnt_a: int = 0;
    let mut cnt_i: int = 0;
    let mut i: int = 0;
    while i < statuses@.len()
        invariant
            i <= statuses@.len(),
            cnt_a == count_status(statuses@.take(i), 'A'),
            cnt_i == count_status(statuses@.take(i), 'I')
        decreases statuses@.len() - i
    {
        if statuses@[i] == 'A' {
            cnt_a = cnt_a + 1;
        } else if statuses@[i] == 'I' {
            cnt_i = cnt_i + 1;
        }
        i = i + 1;
    }
    proof {
        assert(cnt_a == count_status(statuses@, 'A'));
        assert(cnt_i == count_status(statuses@, 'I'));
        assert(cnt_a <= statuses@.len() == n as int);
        assert(cnt_a <= 127);
    }
    let cnt_a_i8 = cnt_a as i8;
    let result = if cnt_i == 0 {
        cnt_a_i8
    } else if cnt_i == 1 {
        1 as i8
    } else {
        0 as i8
    };
    result
}
// </vc-code>


}

fn main() {}