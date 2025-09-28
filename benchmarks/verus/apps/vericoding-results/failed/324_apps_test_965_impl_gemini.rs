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
/* helper modified by LLM (iteration 4): [removed calls to non-existent vstd::seq_lib lemmas] */
proof fn lemma_seq_count_push(s: Seq<char>, new_elt: char, target: char)
    ensures
        seq_count(s.push(new_elt), target) ==
            if new_elt == target {
                seq_count(s, target) + 1
            } else {
                seq_count(s, target)
            },
    decreases s.len()
{
    if s.len() > 0 {
        lemma_seq_count_push(s.drop_first(), new_elt, target);
    }
}

/* helper modified by LLM (iteration 3): [added lemma to bound count with sequence length] */
proof fn lemma_count_le_len(s: Seq<char>, target: char)
    ensures seq_count(s, target) <= s.len()
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_le_len(s.drop_first(), target);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, statuses: Vec<char>) -> (result: i8)
    requires valid_input(n as int, statuses@)
    ensures result as int == expected_result(statuses@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): [no changes; re-verifying with fixed helpers] */
{
    let mut i: usize = 0;
    let mut count_i: usize = 0;
    let mut count_a: usize = 0;

    while i < statuses.len()
        invariant
            0 <= i <= statuses.len(),
            count_i as int == count_status(statuses@.subrange(0, i as int), 'I'),
            count_a as int == count_status(statuses@.subrange(0, i as int), 'A'),
        decreases statuses.len() - i
    {
        let current_status = statuses[i];

        proof {
            let sub = statuses@.subrange(0, i as int);
            let elem = statuses@[i as int];
            lemma_seq_count_push(sub, elem, 'I');
            lemma_seq_count_push(sub, elem, 'A');
        }

        if current_status == 'I' {
            count_i = count_i + 1;
        } else if current_status == 'A' {
            count_a = count_a + 1;
        }
        
        i = i + 1;
    }

    if count_i == 0 {
        proof {
            lemma_count_le_len(statuses@, 'A');
        }
        return count_a as i8;
    } else if count_i == 1 {
        return 1;
    } else {
        return 0;
    }
}
// </vc-code>


}

fn main() {}