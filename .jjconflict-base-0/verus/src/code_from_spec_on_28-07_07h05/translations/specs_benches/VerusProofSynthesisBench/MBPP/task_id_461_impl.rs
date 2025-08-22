use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> (result: bool) {
    (c as u32) >= 97 && (c as u32) <= 122
}
// pure-end

spec fn is_upper_case(c: char) -> (result: bool) {
    (c as u32) >= 65 && (c as u32) <= 90
}
// pure-end

/* code modified by LLM (iteration 4): Added executable version of is_upper_case for use in implementation */
fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    (c as u32) >= 65 && (c as u32) <= 90
}

spec fn count_uppercase_recursively(seq: Seq<char>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

/* code modified by LLM (iteration 4): Added helper spec function for counting from beginning */
spec fn count_uppercase_prefix(seq: Seq<char>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        (if is_upper_case(seq[0]) { 1 as int } else { 0 as int }) + count_uppercase_prefix(seq.skip(1))
    }
}

/* code modified by LLM (iteration 4): Fixed lemma to prove equivalence between prefix and suffix counting */
proof fn lemma_count_equivalence(seq: Seq<char>)
    ensures count_uppercase_recursively(seq) == count_uppercase_prefix(seq)
    decreases seq.len()
{
    if seq.len() == 0 {
        // Base case: both return 0
    } else if seq.len() == 1 {
        // Single element case
        assert(seq[0] == seq.last());
        assert(seq.skip(1).len() == 0);
        assert(seq.drop_last().len() == 0);
    } else {
        // Inductive case for sequences of length > 1
        lemma_count_equivalence(seq.drop_last());
        lemma_count_equivalence(seq.skip(1));
        
        // Key insight: for sequences of length > 1, we need to show the relationship
        // between counting from start vs end by proving they count the same elements
        assert(seq.drop_last().skip(1) == seq.skip(1).drop_last());
        lemma_count_equivalence(seq.drop_last().skip(1));
    }
}

/* code modified by LLM (iteration 4): Added helper lemma for take operations */
proof fn lemma_take_count(seq: Seq<char>, n: int)
    requires 0 <= n <= seq.len()
    ensures count_uppercase_recursively(seq.take(n)) == count_uppercase_prefix(seq.take(n))
    decreases n
{
    lemma_count_equivalence(seq.take(n));
}

/* code modified by LLM (iteration 4): Added lemma to show take(i+1) relationship */
proof fn lemma_take_increment(seq: Seq<char>, i: int)
    requires 0 <= i < seq.len()
    ensures count_uppercase_recursively(seq.take(i + 1)) == 
            count_uppercase_recursively(seq.take(i)) + 
            (if is_upper_case(seq[i]) { 1 as int } else { 0 as int })
{
    let prefix = seq.take(i + 1);
    assert(prefix.len() == i + 1);
    assert(prefix.drop_last() == seq.take(i));
    assert(prefix.last() == seq[i]);
}

fn count_uppercase(text: &Vec<char>) -> (count: u64)
    // post-conditions-start
    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
    // post-conditions-end
{
    let mut count: u64 = 0;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 4): Updated loop with correct invariant and proof annotations */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count == count_uppercase_recursively(text@.take(i as int)),
        decreases text.len() - i,
    {
        /* code modified by LLM (iteration 4): Added proof to maintain loop invariant */
        proof {
            lemma_take_increment(text@, i as int);
        }
        
        if is_upper_case_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 4): Added final proof for postcondition */
    proof {
        assert(i == text.len());
        assert(text@.take(i as int) == text@);
    }
    
    count
}

} // verus!

fn main() {}