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
/* code modified by LLM (iteration 5): Fixed seq.subslice() to seq.subsequence() and used '@' for indexing. */
{
    let n_i8 = n;
    let statuses_seq = statuses@;

    let mut cnt_i: i8 = 0;
    let mut cnt_a: i8 = 0;

    let mut i: i8 = 0;
    while i < n_i8
        invariant
            0 <= i as int,
            i as int <= n_i8 as int,
            cnt_i as int == seq_count(statuses_seq.subsequence(0, i as int), 'I'),
            cnt_a as int == seq_count(statuses_seq.subsequence(0, i as int), 'A'),
            statuses_seq.len() == n_i8 as int,
            forall|j: int| 0 <= j < statuses_seq.len() ==> (statuses_seq[j] == 'A' || statuses_seq[j] == 'I' || statuses_seq[j] == 'F'),
        decreases n_i8 as int - i as int
    {
        let current_status = statuses_seq@[i as int];
        if current_status == 'I' {
            cnt_i = (cnt_i + 1) as i8;
        } else if current_status == 'A' {
            cnt_a = (cnt_a + 1) as i8;
        }
        i = (i + 1) as i8;
    }

    if cnt_i == 0 {
        cnt_a
    } else if cnt_i == 1 {
        1i8
    } else {
        0i8
    }
}
// </vc-code>


}

fn main() {}