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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, statuses: Vec<char>) -> (result: i8)
    requires valid_input(n as int, statuses@)
    ensures result as int == expected_result(statuses@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): restructured to single loop with early termination and i8 counts */
    let len = statuses.len();
    assert(len <= 127);   // because n is i8 and n>=2, so len is at most 127

    let mut i: usize = 0;
    let mut cnt_i: i8 = 0;
    let mut cnt_a: i8 = 0;
    while i < len
        invariant
            0 <= i <= len,
            cnt_i as int == seq_count(statuses@.subrange(0, i as int), 'I'),
            cnt_a as int == seq_count(statuses@.subrange(0, i as int), 'A'),
            cnt_i >= 0,
            cnt_a >= 0,
            cnt_i <= 1,
        decreases len - i
    {
        if statuses[i] == 'I' {
            cnt_i += 1;
            if cnt_i == 2 {
                return 0;
            }
        } else if statuses[i] == 'A' {
            cnt_a += 1;
        }
        i += 1;
    }
    if cnt_i == 0 {
        cnt_a
    } else {
        1
    }
}
// </vc-code>


}

fn main() {}