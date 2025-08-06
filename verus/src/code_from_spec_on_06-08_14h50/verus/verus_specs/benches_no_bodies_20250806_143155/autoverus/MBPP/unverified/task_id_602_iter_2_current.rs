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
    let mut count = 0;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            count == count_frequency_rcr(arr@.take(i as int), key),
    {
        if arr[i] == key {
            count += 1;
        }
        i += 1;
    }
    
    proof {
        assert(arr@.take(arr.len() as int) =~= arr@);
    }
    
    count
}

fn first_repeated_char(str1: &[u8]) -> (repeated_char: Option<(usize, u8)>)
    ensures
        if let Some((idx, rp_char)) = repeated_char {
            /* code modified by LLM (iteration 1): fixed type mismatch by using int indexing for sequence access */
            idx < str1.len() && str1@[idx as int] == rp_char && count_frequency_rcr(str1@, rp_char) > 1 &&
            forall|k: int| 0 <= k < idx ==> count_frequency_rcr(str1@, #[trigger] str1@[k]) <= 1
        } else {
            forall|k: int|
                0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1@[k]) <= 1
        },
{
    let mut index = 0;
    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            forall|k: int| 0 <= k < index ==> count_frequency_rcr(str1@, #[trigger] str1@[k]) <= 1,
    {
        if count_frequency(&str1, str1[index]) > 1 {
            return Some((index, str1[index]));
        }
        index += 1;
    }
    None
}

} // verus!