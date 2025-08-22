use vstd::prelude::*;

fn main() {}

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
    let mut index = 0;
    while index < str1.len() {
        if count_frequency(&str1, str1[index]) > 1 {
            return Some((index, str1[index]));
        }
        index += 1;
    }
    None
}

} // verus!
