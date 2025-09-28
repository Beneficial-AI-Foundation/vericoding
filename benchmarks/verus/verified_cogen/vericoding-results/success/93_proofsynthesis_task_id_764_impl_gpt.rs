// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_digit(c: char) -> (result: bool) {
    (c as u8) >= 48 && (c as u8) <= 57
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add explicit int literals to resolve type inference */
proof fn lemma_count_take_step(seq: Seq<char>, i: int)
    requires
        0 <= i < seq.len(),
    ensures
        count_digits_recursively(seq.take(i + 1))
            == count_digits_recursively(seq.take(i))
                + if is_digit(seq[i]) { 1 as int } else { 0 as int }
{
    assert(count_digits_recursively(seq.take(i + 1))
        == count_digits_recursively(seq.take(i + 1).drop_last())
            + if is_digit(seq.take(i + 1).last()) { 1 as int } else { 0 as int });
    assert(seq.take(i + 1).drop_last() == seq.take(i));
    assert(seq.take(i + 1).last() == seq[i]);
}
// </vc-helpers>

// <vc-spec>
fn count_digits(text: &Vec<char>) -> (count: usize)

    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented counting loop with invariant tied to spec and used helper lemma */
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    while i < text.len()
        invariant
            i <= text.len(),
            0 <= cnt <= i,
            count_digits_recursively(text@.take(i as int)) == cnt,
        decreases text.len() - i
    {
        let c = text[i];
        assert(c == text@[i as int]);
        let is_d = ((c as u8) >= 48u8) && ((c as u8) <= 57u8);
        assert(is_d == is_digit(c));
        proof { lemma_count_take_step(text@, i as int); }
        if is_d {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    assert(i == text.len());
    assert(text@.take(text.len() as int) == text@);
    cnt
}
// </vc-code>

}
fn main() {}