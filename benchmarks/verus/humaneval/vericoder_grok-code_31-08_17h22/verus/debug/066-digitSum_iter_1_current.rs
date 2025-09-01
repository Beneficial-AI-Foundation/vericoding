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
// No additional helpers needed as the implementation aligns directly with the recursive spec.
// </vc-helpers>

// <vc-spec>
fn digit_sum(text: &[char]) -> (sum: u128)
    // post-conditions-start
    ensures
        count_uppercase_sum(text@) == sum,
    // post-conditions-end
// </vc-spec>
// <vc-code>
fn digit_sum(text: &[char]) -> (sum: u128)
    decreases(text.len(),)
{
    if text.len() == 0 {
        0
    } else {
        proof_assert!(text.len() as int > 0);
        let rec = digit_sum(&text[0..text.len() - 1]);
        let last = text[text.len() - 1];
        if is_upper_case(last) {
            rec + (last as u128)
        } else {
            rec
        }
    }
}
// </vc-code>

} // verus!
fn main() {}