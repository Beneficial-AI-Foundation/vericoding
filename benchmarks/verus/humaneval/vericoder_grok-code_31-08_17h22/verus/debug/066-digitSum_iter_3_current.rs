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
spec fn stop_at_edge(full_seq: Seq<u128>, partial_sum: u128, index: usize) -> bool
    decreases full_seq.len() - index,
{
    // Placeholder helper to support loop invariant proofs
    partial_sum == full_sum(full_seq.subrange(0, index as int))
}

spec fn full_sum(seq: Seq<u128>) -> u128
    decreases seq,
{
    if seq.len() == 0 {
        0
    } else {
        full_sum(seq.drop_last()) + seq.last()
    }
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
fn digit_sum(text: &[char]) -> (sum: u128) {
    let mut sum = 0u128;
    let mut i = 0usize;
    while i < text.len()
        decreases text.len() as int - i as int,
    {
        invariant
            i <= text.len() as int,
            sum as int == count_uppercase_sum(text@.subrange(0, i as int));
        if is_upper_case(text[i]) {
            sum += text[i] as u128;
        }
        i += 1;
    }
    sum
}
// </vc-code>

} // verus!
fn main() {}