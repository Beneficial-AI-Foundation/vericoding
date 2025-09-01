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

// Helper function to convert slice to Seq<char>
spec fn slice_to_seq(slice: &[char]) -> Seq<char> {
    Seq::new(slice.len() as nat, |j| slice[j])
}

// Lemma to relate slice_to_seq and sub_seq
proof fn slice_to_seq_sub_seq_lemma(slice: &[char], start: int, end: int)
    requires
        0 <= start <= end as int,
        end <= slice.len() as int,
    ensures
        slice_to_seq(slice).sub_seq(start, end) == slice_to_seq(&slice[start as usize .. end as usize]),
{
    // This lemma states that taking a sub_seq of a sequence derived from a slice
    // is equivalent to deriving a sequence from the corresponding sub-slice.
    // Verus often needs explicit proof for these kinds of equivalences.
    assert_seq_to_rust_slice_relation(&slice[start as usize .. end as usize]);
    assert(slice_to_seq(&slice[start as usize .. end as usize]).len() == (end - start) as nat);
    assert(slice_to_seq(slice).sub_seq(start, end).len() == (end - start) as nat);

    if end > start {
        assert(slice_to_seq(slice).sub_seq(start, end).ext_equal(Seq::new((end - start) as nat, |j: nat| slice[(start + j) as usize])));
        assert(slice_to_seq(&slice[start as usize .. end as usize]).ext_equal(Seq::new((end - start) as nat, |j: nat| slice[(start + j) as usize])));
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
{
    let mut sum: u128 = 0;
    let mut i: usize = 0;

    let text_seq = slice_to_seq(text);

    while i < text.len()
        invariant
            0 <= i as int,
            i as int <= text.len() as int,
            sum as int == count_uppercase_sum(text_seq.sub_seq(0, i as int)),
            // Add a trigger for text_seq.sub_seq
            // #[trigger] text_seq.sub_seq(0, i as int),
    {
        let c = text[i];
        if is_upper_case_char(c) {
            sum = sum + (c as u128);
            proof {
                assert (count_uppercase_sum(text_seq.sub_seq(0, (i + 1) as int)) ==
                        count_uppercase_sum(text_seq.sub_seq(0, i as int)) + (c as int));
            }
        } else {
            proof {
                assert (count_uppercase_sum(text_seq.sub_seq(0, (i + 1) as int)) ==
                        count_uppercase_sum(text_seq.sub_seq(0, i as int)));
            }
        }
        i = i + 1;
    }
    assert(sum as int == count_uppercase_sum(text_seq.sub_seq(0, i as int)));
    assert(i as int == text.len() as int);
    assert(text_seq.sub_seq(0, i as int) == text_seq); // When i reaches text.len()

    sum
}
// </vc-code>

} // verus!
fn main() {}