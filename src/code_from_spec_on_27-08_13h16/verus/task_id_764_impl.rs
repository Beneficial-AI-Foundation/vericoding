use vstd::prelude::*;


verus! {

spec fn is_digit(c: char) -> (result: bool) {
    (c as u8) >= 48 && (c as u8) <= 57
}
// pure-end
// pure-end

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

// <vc-helpers>
proof fn lemma_count_digits_recursively_non_negative(seq: Seq<char>)
    decreases seq.len()
    ensures count_digits_recursively(seq) >= 0
{
    if seq.len() > 0 {
        lemma_count_digits_recursively_non_negative(seq.drop_last());
    }
}
// </vc-helpers>

// <vc-spec>
fn count_digits(text: &Vec<char>) -> (count: usize)
    // pre-conditions-start
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
    // pre-conditions-end
// </vc-spec>

// <vc-code>
fn count_digits(text: &Vec<char>) -> (count: usize)
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
{
    let mut count: usize = 0;
    let mut i: usize = 0;

    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count_digits_recursively(text@.subrange(0, i as int)) == count,
    {
        if is_digit(text@[i]) {
            count = count + 1;
        }
        i = i + 1;
    }

    proof {
        lemma_count_digits_recursively_non_negative(text@);
    }

    count
}
// </vc-code>

} // verus!

fn main() {}