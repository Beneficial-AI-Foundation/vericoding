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
    let mut sum = 0u128;
    let mut i = 0;
    while i < text.len() {
        // invariant: sum == count_uppercase_sum(text@[0..i])
        if is_upper_case(text[i]) {
            assert!( (text[i] as u128) == (text[i] as int as u128) );
            sum = sum + (text[i] as u128);
        }
        i = i + 1;
    }
    sum
}
// </vc-code>

} // verus!
fn main() {}