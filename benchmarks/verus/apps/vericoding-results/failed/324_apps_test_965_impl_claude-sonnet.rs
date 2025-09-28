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
/* helper modified by LLM (iteration 5): Added decreases clause to while loop */
proof fn seq_count_bounds(s: Seq<char>, target: char)
    ensures 0 <= seq_count(s, target) <= s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        seq_count_bounds(s.drop_first(), target);
    }
}

proof fn seq_count_add_one(s: Seq<char>, target: char, c: char)
    ensures seq_count(s.push(c), target) == seq_count(s, target) + if c == target { 1int } else { 0int }
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        seq_count_add_one(s.drop_first(), target, c);
    }
}

fn count_chars(statuses: &Vec<char>, target: char) -> (count: i8)
    requires statuses.len() <= 127,
        forall|i: int| 0 <= i < statuses@.len() ==> (statuses@[i] == 'A' || statuses@[i] == 'I' || statuses@[i] == 'F')
    ensures count as int == seq_count(statuses@, target)
{
    let mut count = 0i8;
    let mut i = 0;
    
    while i < statuses.len()
        invariant
            0 <= i <= statuses.len(),
            count as int == seq_count(statuses@.take(i as int), target),
            forall|j: int| 0 <= j < statuses@.len() ==> (statuses@[j] == 'A' || statuses@[j] == 'I' || statuses@[j] == 'F')
        decreases statuses.len() - i
    {
        proof {
            seq_count_add_one(statuses@.take(i as int), target, statuses@[i as int]);
        }
        if statuses[i] == target {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(statuses@.take(i as int) == statuses@);
    }
    
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, statuses: Vec<char>) -> (result: i8)
    requires valid_input(n as int, statuses@)
    ensures result as int == expected_result(statuses@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed implementation with proper proof structure */
    let cnt_i = count_chars(&statuses, 'I');
    let cnt_a = count_chars(&statuses, 'A');
    
    if cnt_i == 0 {
        cnt_a
    } else if cnt_i == 1 {
        1
    } else {
        0
    }
}
// </vc-code>


}

fn main() {}