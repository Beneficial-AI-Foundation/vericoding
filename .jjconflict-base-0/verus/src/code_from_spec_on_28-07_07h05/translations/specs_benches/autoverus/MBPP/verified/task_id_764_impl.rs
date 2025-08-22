use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

spec fn is_digit(c: u8) -> bool {
    (c >= 48 && c <= 57)
}

/* code modified by LLM (iteration 3): Added executable version of is_digit function */
fn is_digit_exec(c: u8) -> (result: bool)
    ensures result == is_digit(c)
{
    c >= 48 && c <= 57
}

spec fn count_digits_recursively(seq: Seq<u8>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_digits_recursively(seq.drop_last()) + if is_digit(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

/* code modified by LLM (iteration 3): Added helper lemma to relate subrange operations */
proof fn lemma_count_digits_extend(seq: Seq<u8>, i: int)
    requires 0 <= i < seq.len()
    ensures count_digits_recursively(seq.subrange(0, i + 1)) == 
            count_digits_recursively(seq.subrange(0, i)) + if is_digit(seq[i]) { 1 } else { 0 }
    decreases seq.len() - i
{
    let prefix_i = seq.subrange(0, i);
    let prefix_i_plus_1 = seq.subrange(0, i + 1);
    
    if i == 0 {
        assert(prefix_i.len() == 0);
        assert(prefix_i_plus_1.len() == 1);
        assert(prefix_i_plus_1[0] == seq[0]);
    } else {
        assert(prefix_i_plus_1 == prefix_i.push(seq[i]));
        lemma_count_digits_push(prefix_i, seq[i]);
    }
}

/* code modified by LLM (iteration 3): Added helper lemma for push operation */
proof fn lemma_count_digits_push(seq: Seq<u8>, elem: u8)
    ensures count_digits_recursively(seq.push(elem)) == 
            count_digits_recursively(seq) + if is_digit(elem) { 1 } else { 0 }
{
    if seq.len() == 0 {
        assert(seq.push(elem).len() == 1);
        assert(seq.push(elem).last() == elem);
        assert(seq.push(elem).drop_last() == seq);
    } else {
        assert(seq.push(elem).last() == elem);
        assert(seq.push(elem).drop_last() == seq);
    }
}

/* code modified by LLM (iteration 3): Added lemma to connect final subrange with full sequence */
proof fn lemma_full_sequence_equals_subrange(seq: Seq<u8>)
    ensures seq.subrange(0, seq.len() as int) == seq
{
}

fn count_digits(text: &[u8]) -> (count: usize)
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
{
    let mut count = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): Updated loop with corrected invariant and proof annotations */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count == count_digits_recursively(text@.subrange(0, i as int)),
        decreases text.len() - i,
    {
        /* code modified by LLM (iteration 4): Fixed lemma call by removing problematic cast */
        lemma_count_digits_extend(text@, i);
        
        if is_digit_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 3): Added final proof to establish postcondition */
    lemma_full_sequence_equals_subrange(text@);
    
    count
}

} // verus!