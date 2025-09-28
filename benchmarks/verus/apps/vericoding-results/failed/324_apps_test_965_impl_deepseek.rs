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
/* helper modified by LLM (iteration 5): Fixed compilation error by adding proper function signature with requires block */
proof fn seq_count_lemma(s: Seq<char>, target: char, i: int)
    decreases s.len() - i
    requires
        0 <= i <= s.len(),
    ensures
        seq_count(s.take(i), target) + seq_count(s.subrange(i, s.len() as int), target) == seq_count(s, target),
{
    if i == 0 {
        assert(s.take(0) =~= Seq::empty());
        assert(s.subrange(0, s.len() as int) =~= s);
        assert(seq_count(s.take(0), target) == 0);
    } else {
        seq_count_lemma(s, target, i - 1);
        let prev = s.take(i - 1);
        let remaining = s.subrange(i - 1, s.len() as int);
        let current_char = s[i - 1];
        let remaining_new = s.subrange(i, s.len() as int);
        
        if current_char == target {
            assert(seq_count(prev.push(current_char), target) == seq_count(prev, target) + 1);
            assert(seq_count(remaining, target) == seq_count(Seq::empty().push(current_char).add(remaining_new), target));
        } else {
            assert(seq_count(prev.push(current_char), target) == seq_count(prev, target));
        }
        assert(seq_count(s, target) == seq_count(s.take(i), target) + seq_count(remaining_new, target));
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
    /* code modified by LLM (iteration 5): Fixed compilation error with proper while loop syntax */
    let mut count_i: i8 = 0;
    let mut count_a: i8 = 0;
    let len = statuses.len();
    let mut i: usize = 0;
    
    while i < len
        invariant
            0 <= i <= len,
            count_i as int == count_status(statuses@.take(i as int), 'I'),
            count_a as int == count_status(statuses@.take(i as int), 'A'),
    {
        let c = statuses[i];
        proof {
            seq_count_lemma(statuses@, 'I', i as int);
            seq_count_lemma(statuses@, 'A', i as int);
        }
        
        if c == 'I' {
            count_i += 1;
        } else if c == 'A' {
            count_a += 1;
        }
        
        let old_i = i;
        i += 1;
        
        proof {
            if c == 'I' {
                assert(count_status(statuses@.take(i as int), 'I') == count_status(statuses@.take(old_i as int), 'I') + 1);
            } else {
                assert(count_status(statuses@.take(i as int), 'I') == count_status(statuses@.take(old_i as int), 'I'));
            }
            if c == 'A' {
                assert(count_status(statuses@.take(i as int), 'A') == count_status(statuses@.take(old_i as int), 'A') + 1);
            } else {
                assert(count_status(statuses@.take(i as int), 'A') == count_status(statuses@.take(old_i as int), 'A'));
            }
        }
    }
    
    proof {
        let len_int = len as int;
        assert(i == len);
        assert(statuses@.take(len_int) =~= statuses@);
        assert(count_i as int == count_status(statuses@, 'I'));
        assert(count_a as int == count_status(statuses@, 'A'));
    }
    
    if count_i == 0 {
        count_a
    } else if count_i == 1 {
        1
    } else {
        0
    }
}
// </vc-code>


}

fn main() {}