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
    if text.len() == 0 {
        0u128
    } else {
        let last_idx = text.len() - 1;
        let rest_sum = digit_sum(&text[..last_idx]);
        let last = text[last_idx];
        let add = if last >= 'A' && last <= 'Z' { last as u128 } else { 0u128 };

        proof {
            // Basic correspondences between slice and sequence views
            assert(text@.len() == text.len() as int);
            assert((&text[..last_idx])@ == text@.take(last_idx as int));
            assert(text@.drop_last() == text@.take(text@.len() - 1));
            assert(text@.last() == last);

            // Definition unfolding for the recursive spec function on non-empty sequences
            assert(text@.len() > 0);
            assert(
                count_uppercase_sum(text@)
                ==
                count_uppercase_sum(text@.drop_last())
                + if is_upper_case(text@.last()) { text@.last() as int } else { 0 as int }
            );

            // Bridge executable condition and spec predicate
            assert(is_upper_case(last) == (last >= 'A' && last <= 'Z'));
        }

        rest_sum + add
    }
}
// </vc-code>

} // verus!
fn main() {}