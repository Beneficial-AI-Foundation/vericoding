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

proof fn lemma_count_uppercase_sum_append(seq: Seq<char>, c: char)
    ensures count_uppercase_sum(seq.push(c)) == count_uppercase_sum(seq) + if is_upper_case(c) { c as int } else { 0 }
{
    if seq.len() == 0 {
        assert(seq.push(c) =~= seq![c]);
        assert(count_uppercase_sum(seq.push(c)) == count_uppercase_sum(seq![c]));
        assert(seq![c].last() == c);
        assert(count_uppercase_sum(seq![c]) == 0 + if is_upper_case(c) { c as int } else { 0 });
    } else {
        let extended = seq.push(c);
        assert(extended.drop_last() =~= seq);
        assert(extended.last() == c);
        assert(count_uppercase_sum(extended) == count_uppercase_sum(seq) + if is_upper_case(c) { c as int } else { 0 });
    }
}

proof fn lemma_count_uppercase_sum_prefix(seq: Seq<char>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_uppercase_sum(seq.subrange(0, i)) == 
        if i == 0 { 0 } else { 
            count_uppercase_sum(seq.subrange(0, i - 1)) + if is_upper_case(seq[i - 1]) { seq[i - 1] as int } else { 0 }
        }
{
    if i == 0 {
        assert(seq.subrange(0, 0) =~= Seq::<char>::empty());
    } else {
        let prefix = seq.subrange(0, i);
        let prev_prefix = seq.subrange(0, i - 1);
        assert(prefix =~= prev_prefix.push(seq[i - 1]));
        lemma_count_uppercase_sum_append(prev_prefix, seq[i - 1]);
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
    let mut i: usize = 0;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            sum == count_uppercase_sum(text@.subrange(0, i as int)),
    {
        let c = text[i];
        if is_upper_case_exec(c) {
            sum = sum + (c as u128);
        }
        
        proof {
            lemma_count_uppercase_sum_prefix(text@, (i + 1) as int);
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