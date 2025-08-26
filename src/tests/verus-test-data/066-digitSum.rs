use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (ret:bool) {
    c >= 'A' && c <= 'Z'
}
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

fn digit_sum(text: &[char]) -> (sum: u128)
    // post-conditions-start
    ensures
        count_uppercase_sum(text@) == sum,
    // post-conditions-end
{
    // impl-start
    let mut index = 0;
    let mut sum = 0u128;

    while index < text.len()
        // invariants-start
        invariant
            0 <= index <= text.len(),
            count_uppercase_sum(text@.subrange(0, index as int)) == sum,
            forall|j: int|
                0 <= j <= index ==> (u64::MIN * index <= (count_uppercase_sum(
                    #[trigger] text@.subrange(0, j),
                )) <= u64::MAX * index),
            u64::MIN * index <= sum <= u64::MAX * index,
        // invariants-end
    {
        if (text[index] >= 'A' && text[index] <= 'Z') {
            // assert-start
            assert(text@.subrange(0, index as int) =~= text@.subrange(
                0,
                (index + 1) as int,
            ).drop_last());
            // assert-end
            sum = sum + text[index] as u128;
        }
        index += 1;
        assert(text@.subrange(0, index - 1 as int) == text@.subrange(0, index as int).drop_last()); // assert-line
    }
    // assert-start
    assert(index == text@.len());
    assert(text@ == text@.subrange(0, index as int));
    // assert-end
    sum
    // impl-end
}

} // verus!
fn main() {}