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
fn is_upper_case_char(c: char) -> (ret: bool) {
    c >= 'A' && c <= 'Z'
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
            0 <= i as int,
            i as int <= text.len() as int,
            sum == count_uppercase_sum(text.subsequence(0, i as int)),
    {
        let c = text[i];
        if is_upper_case_char(c) {
            sum = sum + (c as u128);
        }
        i = i + 1;
    }
    sum
}
// </vc-code>

} // verus!
fn main() {}