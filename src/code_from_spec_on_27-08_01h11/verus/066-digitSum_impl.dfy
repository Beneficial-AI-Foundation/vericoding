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
proof fn count_uppercase_sum_append_lemma(seq: Seq<char>, c: char)
    ensures count_uppercase_sum(seq.push(c)) == count_uppercase_sum(seq) + if is_upper_case(c) { c as int } else { 0 }
    decreases seq.len()
{
    if seq.len() == 0 {
        assert(seq.push(c) =~= seq![c]);
        assert(seq.push(c).drop_last() =~= seq![]);
        assert(seq.push(c).last() == c);
    } else {
        let seq_extended = seq.push(c);
        assert(seq_extended.drop_last() =~= seq.drop_last().push(c));
        assert(seq_extended.last() == c);
        count_uppercase_sum_append_lemma(seq.drop_last(), c);
    }
}

proof fn count_uppercase_sum_slice_lemma(text: &[char], i: usize)
    requires i < text.len()
    ensures count_uppercase_sum(text@.subrange(0, i as int).push(text@[i as int])) == 
            count_uppercase_sum(text@.subrange(0, i as int)) + if is_upper_case(text@[i as int]) { text@[i as int] as int } else { 0 }
{
    count_uppercase_sum_append_lemma(text@.subrange(0, i as int), text@[i as int]);
}

fn is_upper_case_exec(c: char) -> (ret: bool)
    ensures ret == is_upper_case(c)
{
    c >= 'A' && c <= 'Z'
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
            i <= text.len(),
            sum == count_uppercase_sum(text@.subrange(0, i as int)),
        decreases text.len() - i
    {
        let c = text[i];
        
        if is_upper_case_exec(c) {
            sum = sum + (c as u128);
        }
        
        proof {
            assert(text@.subrange(0, i as int + 1) =~= text@.subrange(0, i as int).push(text@[i as int]));
            count_uppercase_sum_slice_lemma(text, i);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(text@.subrange(0, text.len() as int) =~= text@);
    }
    
    sum
}
// </vc-code>

} // verus!
fn main() {}