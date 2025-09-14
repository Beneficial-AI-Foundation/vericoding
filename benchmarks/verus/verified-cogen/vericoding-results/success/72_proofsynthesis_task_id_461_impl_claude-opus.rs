// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> (result: bool) {
    (c as u32) >= 97 && (c as u32) <= 122
}

spec fn is_upper_case(c: char) -> (result: bool) {
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
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_uppercase_extend(seq: Seq<char>, c: char)
    ensures
        count_uppercase_recursively(seq.push(c)) == count_uppercase_recursively(seq) + if is_upper_case(c) { 1int } else { 0int },
    decreases seq.len(),
{
    /* helper modified by LLM (iteration 5): fixed integer literal type annotations */
    if seq.len() == 0 {
        assert(seq.push(c).drop_last() == seq);
        assert(seq.push(c).last() == c);
    } else {
        assert(seq.push(c).drop_last() == seq);
        assert(seq.push(c).last() == c);
    }
}
// </vc-helpers>

// <vc-spec>
fn count_uppercase(text: &Vec<char>) -> (count: u64)

    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implementation with proper loop invariant */
    let mut count: u64 = 0;
    let mut i: usize = 0;
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            0 <= count <= i,
            count == count_uppercase_recursively(text@.take(i as int)),
        decreases text.len() - i,
    {
        let c = text[i];
        let old_count = count;
        if #[verifier::truncate] (c as u32) >= 65 && #[verifier::truncate] (c as u32) <= 90 {
            count = count + 1;
        }
        proof {
            assert(text@.take(i as int).push(text@[i as int]) == text@.take((i + 1) as int));
            lemma_count_uppercase_extend(text@.take(i as int), c);
            if is_upper_case(c) {
                assert(count == old_count + 1);
                assert(count_uppercase_recursively(text@.take((i + 1) as int)) == count_uppercase_recursively(text@.take(i as int)) + 1);
            } else {
                assert(count == old_count);
                assert(count_uppercase_recursively(text@.take((i + 1) as int)) == count_uppercase_recursively(text@.take(i as int)));
            }
        }
        i = i + 1;
    }
    assert(text@.take(text.len() as int) == text@);
    count
}
// </vc-code>

}
fn main() {}