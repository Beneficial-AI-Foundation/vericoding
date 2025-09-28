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
/* helper modified by LLM (iteration 5): fixed postcondition proofs for seq_count helpers */
proof fn seq_count_bounds(s: Seq<char>, target: char)
    ensures 0 <= seq_count(s, target) <= s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        seq_count_bounds(s.drop_first(), target);
    }
}

proof fn seq_count_take_push(s: Seq<char>, i: int, target: char)
    requires
        0 <= i < s.len(),
    ensures
        seq_count(s.take(i + 1), target) == seq_count(s.take(i), target) + if s[i] == target { 1int } else { 0int },
    decreases i
{
    if i == 0 {
        assert(s.take(0) == Seq::<char>::empty());
        assert(s.take(1).len() == 1);
        assert(s.take(1) == seq![s[0]]);
        assert(seq_count(s.take(0), target) == 0);
        assert(seq_count(s.take(1), target) == if s[0] == target { 1 } else { 0 });
    } else {
        seq_count_take_push(s, i - 1, target);
        assert(s.take(i + 1) == s.take(i).push(s[i]));
        seq_count_take_push_helper(s.take(i), s[i], target);
    }
}

proof fn seq_count_take_push_helper(s: Seq<char>, c: char, target: char)
    ensures seq_count(s.push(c), target) == seq_count(s, target) + if c == target { 1int } else { 0int }
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(c) == seq![c]);
        assert(seq_count(seq![c], target) == if c == target { 1 } else { 0 });
    } else {
        let s_push = s.push(c);
        assert(s_push[0] == s[0]);
        assert(s_push.drop_first() == s.drop_first().push(c));
        seq_count_take_push_helper(s.drop_first(), c, target);
        assert(seq_count(s_push, target) == if s_push[0] == target { 1 } else { 0 } + seq_count(s_push.drop_first(), target));
        assert(seq_count(s, target) == if s[0] == target { 1 } else { 0 } + seq_count(s.drop_first(), target));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, statuses: Vec<char>) -> (result: i8)
    requires valid_input(n as int, statuses@)
    ensures result as int == expected_result(statuses@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implementation unchanged from iteration 4 */
    let mut cnt_i: i8 = 0;
    let mut cnt_a: i8 = 0;
    let mut i: usize = 0;
    
    proof {
        seq_count_bounds(statuses@, 'I');
        seq_count_bounds(statuses@, 'A');
        assert(statuses@.len() <= i8::MAX as int);
    }
    
    while i < statuses.len()
        invariant
            0 <= i <= statuses.len(),
            cnt_i as int == seq_count(statuses@.take(i as int), 'I'),
            cnt_a as int == seq_count(statuses@.take(i as int), 'A'),
            valid_input(n as int, statuses@),
            cnt_i >= 0,
            cnt_a >= 0,
            cnt_i as int <= i,
            cnt_a as int <= i,
        decreases statuses.len() - i
    {
        proof {
            seq_count_take_push(statuses@, i as int, 'I');
            seq_count_take_push(statuses@, i as int, 'A');
            seq_count_bounds(statuses@.take((i + 1) as int), 'I');
            seq_count_bounds(statuses@.take((i + 1) as int), 'A');
        }
        
        if statuses[i] == 'I' {
            cnt_i = cnt_i + 1;
        } else if statuses[i] == 'A' {
            cnt_a = cnt_a + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(statuses@.take(statuses.len() as int) == statuses@);
    }
    
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