use vstd::prelude::*;

verus! {

spec fn is_digit(c: char) -> (result: bool) {
    (c as u8) >= 48 && (c as u8) <= 57
}
// pure-end

/* code modified by LLM (iteration 4): Added executable version of is_digit for use in implementation */
fn is_digit_exec(c: char) -> (result: bool)
    ensures result == is_digit(c)
{
    let byte_val = c as u8;
    byte_val >= 48 && byte_val <= 57
}

spec fn count_digits_recursively(seq: Seq<char>) -> (result: int)
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
// pure-end

/* code modified by LLM (iteration 4): Added helper function to count digits from beginning with fixed type annotations */
spec fn count_digits_from_start(seq: Seq<char>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        (if is_digit(seq[0]) { 1int } else { 0int }) + count_digits_from_start(seq.skip(1))
    }
}

/* code modified by LLM (iteration 4): Added lemma to prove equivalence between the two counting methods with fixed sequence operations */
proof fn lemma_count_equivalence(seq: Seq<char>)
    ensures count_digits_recursively(seq) == count_digits_from_start(seq)
    decreases seq.len(),
{
    if seq.len() == 0 {
        // Base case: both return 0
    } else {
        // Inductive step
        lemma_count_equivalence(seq.drop_last());
        lemma_count_equivalence(seq.skip(1));
        
        // The key insight: seq can be viewed as first element + rest, or prefix + last element
        assert(seq.drop_last().push(seq.last()) == seq);
        assert(seq.subrange(0, 1).add(seq.skip(1)) == seq);
    }
}

/* code modified by LLM (iteration 4): Added lemma for prefix counting with fixed type annotations */
proof fn lemma_prefix_count(seq: Seq<char>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_digits_from_start(seq.take(i)) == 
            if i == 0 { 0 } else { 
                count_digits_from_start(seq.take(i-1)) + (if is_digit(seq[i-1]) { 1int } else { 0int })
            }
    decreases i,
{
    if i == 0 {
        // Base case
    } else {
        // seq.take(i) = seq.take(i-1) + seq[i-1]
        lemma_prefix_count(seq, i-1);
    }
}

fn count_digits(text: &Vec<char>) -> (count: usize)
    // pre-conditions-start
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
    // pre-conditions-end
{
    /* code modified by LLM (iteration 4): Added proof that establishes equivalence at the start */
    proof {
        lemma_count_equivalence(text@);
    }
    
    let mut count = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): Updated loop invariant to use count_digits_from_start */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count_digits_from_start(text@.take(i as int)) == count,
        decreases text.len() - i,
    {
        /* code modified by LLM (iteration 4): Added proof block to maintain invariant */
        proof {
            lemma_prefix_count(text@, (i + 1) as int);
        }
        
        /* code modified by LLM (iteration 4): Changed is_digit call to is_digit_exec for executable code */
        if is_digit_exec(text[i]) {
            count += 1;
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 4): Added final proof to convert from count_digits_from_start back to count_digits_recursively */
    proof {
        assert(text@.take(text.len() as int) == text@);
        lemma_count_equivalence(text@);
    }
    
    count
}

} // verus!

fn main() {}