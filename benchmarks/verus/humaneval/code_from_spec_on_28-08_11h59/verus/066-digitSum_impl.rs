use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (ret:bool) {
    c >= 'A' && c <= 'Z'
}
// pure-end
// pure-end

spec fn count_uppercase_sum(seq: Seq<char>) -> (ret:int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_sum(seq.drop_last()) + if is_upper_case(seq.last()) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
proof fn count_uppercase_sum_empty_char()
    ensures count_uppercase_sum(seq![]) == 0
{
}

proof fn count_uppercase_sum_single_char(c: char)
    ensures count_uppercase_sum(seq![c]) == if is_upper_case(c) { c as int } else { 0 }
{
}

proof fn count_uppercase_sum_append_lemma(seq: Seq<char>, c: char)
    ensures count_uppercase_sum(seq.push(c)) == count_uppercase_sum(seq) + if is_upper_case(c) { c as int } else { 0 as int }
{
    if seq.len() == 0 {
        assert(seq.push(c) =~= seq![c]);
        count_uppercase_sum_single_char(c);
        count_uppercase_sum_empty_char();
    } else {
        let seq_push = seq.push(c);
        assert(seq_push.drop_last() =~= seq);
        assert(seq_push.last() == c);
    }
}

fn is_upper_case_exec(c: char) -> (ret: bool)
    ensures ret == is_upper_case(c)
{
    c >= 'A' && c <= 'Z'
}

proof fn char_to_int_bounds(c: char)
    requires is_upper_case(c)
    ensures 65 <= c as int <= 90
{
}
// </vc-helpers>

// <vc-spec>
fn digit_sum(text: &[char]) -> (sum: u128)
    // post-conditions-start
    ensures
        count_uppercase_sum(text@) == sum,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut sum: u128 = 0;
    let mut i: usize = 0;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            sum == count_uppercase_sum(text@.take(i as int)) as u128,
            sum <= i * 90,
        decreases text.len() - i,
    {
        let c = text[i];
        
        proof {
            let prev_seq = text@.take(i as int);
            let new_seq = text@.take((i + 1) as int);
            assert(new_seq =~= prev_seq.push(c));
            count_uppercase_sum_append_lemma(prev_seq, c);
        }
        
        if is_upper_case_exec(c) {
            proof {
                char_to_int_bounds(c);
            }
            sum = sum + (c as u128);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(text@.take(text.len() as int) =~= text@);
    }
    
    sum
}
// </vc-code>

} // verus!
fn main() {}