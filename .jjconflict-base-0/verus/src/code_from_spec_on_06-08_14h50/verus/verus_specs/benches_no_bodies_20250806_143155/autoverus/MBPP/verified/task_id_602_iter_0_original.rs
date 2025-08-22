use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

pub open spec fn count_frequency_rcr(seq: Seq<u8>, key: u8) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_frequency(arr: &[u8], key: u8) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn first_repeated_char(str1: &[u8]) -> (repeated_char: Option<(usize, u8)>)
    ensures
        if let Some((idx, rp_char)) = repeated_char {
    return None;  // TODO: Remove this line and implement the function body
        } else {
            forall|k: int|
                0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1
        },
{
    let input_len = str1.len();
    assert(str1@.take(0int).filter(|x: u8| count_frequency_rcr(str1@, x) > 1) == Seq::<
        u8,
    >::empty());
    let mut index = 0;
    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            str1@.take(index as int) =~= str1@.take(index as int).filter(
                |x: u8| count_frequency_rcr(str1@, x) <= 1,
            ),
    {
        if count_frequency(&str1, str1[index]) > 1 {
            return Some((index, str1[index]));
        }
        assert(str1@.take((index + 1) as int).drop_last() == str1@.take(index as int));
        reveal(Seq::filter);
        index += 1;
    }
    assert(str1@ =~= str1@.take(input_len as int));
    assert(forall|k: int|
        0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1);
    None
}

} // verus!
