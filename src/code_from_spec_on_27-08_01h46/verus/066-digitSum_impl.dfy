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
exec fn is_upper_case_exec(c: char) -> (ret: bool)
    ensures ret == is_upper_case(c)
{
    c >= 'A' && c <= 'Z'
}

proof fn count_uppercase_sum_append_lemma(seq: Seq<char>, c: char)
    ensures count_uppercase_sum(seq.push(c)) == count_uppercase_sum(seq) + if is_upper_case(c) { c as int } else { 0 as int }
    decreases seq.len()
{
    if seq.len() == 0 {
        assert(seq.push(c) =~= seq![c]);
        assert(count_uppercase_sum(seq) == 0);
        assert(count_uppercase_sum(seq.push(c)) == if is_upper_case(c) { c as int } else { 0 as int });
    } else {
        let last_elem = seq.last();
        let seq_without_last = seq.drop_last();
        
        count_uppercase_sum_append_lemma(seq_without_last, c);
        
        assert(seq.push(c) =~= seq_without_last.push(c).push(last_elem));
        assert(seq.push(c).last() == last_elem);
        assert(seq.push(c).drop_last() =~= seq_without_last.push(c));
        
        assert(count_uppercase_sum(seq.push(c)) == 
               count_uppercase_sum(seq_without_last.push(c)) + if is_upper_case(last_elem) { last_elem as int } else { 0 as int });
               
        assert(count_uppercase_sum(seq_without_last.push(c)) == 
               count_uppercase_sum(seq_without_last) + if is_upper_case(c) { c as int } else { 0 as int });
               
        assert(count_uppercase_sum(seq) == 
               count_uppercase_sum(seq_without_last) + if is_upper_case(last_elem) { last_elem as int } else { 0 as int });
    }
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
    let mut i = 0;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            sum == count_uppercase_sum(text@.take(i as int)),
            sum <= i * 255,
        decreases text.len() - i,
    {
        let c = text[i];
        
        proof {
            count_uppercase_sum_append_lemma(text@.take(i as int), c);
            assert(text@.take((i + 1) as int) == text@.take(i as int).push(c));
        }
        
        if is_upper_case_exec(c) {
            sum = sum + (c as u128);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(text@.take(text.len() as int) == text@);
    }
    
    sum
}
// </vc-code>

} // verus!
fn main() {}