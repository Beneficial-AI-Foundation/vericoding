use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_digit(c: u8) -> bool {
    (c >= 48 && c <= 57)
}

/* code modified by LLM (iteration 4): added executable version of is_digit for use in implementation */
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

/* code modified by LLM (iteration 4): removed requires/ensures from spec function */
spec fn count_digits_from_start(seq: Seq<u8>, len: int) -> int
    decreases len
{
    if len <= 0 || len > seq.len() {
        0
    } else {
        count_digits_from_start(seq, len - 1) + if is_digit(seq[len - 1]) {
            1 as int
        } else {
            0 as int
        }
    }
}

/* code modified by LLM (iteration 4): added lemma to prove equivalence between the two counting methods */
proof fn lemma_count_equivalence(seq: Seq<u8>)
    ensures count_digits_recursively(seq) == count_digits_from_start(seq, seq.len() as int)
    decreases seq.len()
{
    if seq.len() == 0 {
        // Base case: both return 0
    } else {
        // Inductive case
        lemma_count_equivalence(seq.drop_last());
        assert(seq.drop_last().len() == seq.len() - 1);
        assert(count_digits_from_start(seq, seq.len() as int - 1) == count_digits_from_start(seq.drop_last(), seq.drop_last().len() as int));
    }
}

fn count_digits(text: &[u8]) -> (count: usize)
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
{
    let mut count = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): updated loop invariant with bounds check for count_digits_from_start */
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count == count_digits_from_start(text@, i as int),
        decreases text.len() - i,
    {
        /* code modified by LLM (iteration 4): replaced is_digit call with is_digit_exec call */
        if is_digit_exec(text[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 4): added proof that the two counting methods are equivalent */
    lemma_count_equivalence(text@);
    assert(count_digits_from_start(text@, text.len() as int) == count_digits_recursively(text@));
    
    count
}

} // verus!