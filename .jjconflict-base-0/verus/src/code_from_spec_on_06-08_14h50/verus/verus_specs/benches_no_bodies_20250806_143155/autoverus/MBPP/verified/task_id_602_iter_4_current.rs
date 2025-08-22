use vstd::prelude::*;

fn main() {
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
    let mut count = 0;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            count == count_frequency_rcr(arr@.take(i as int), key),
    {
        /* code modified by LLM (iteration 1): use usize indexing instead of int cast */
        if arr[i] == key {
            count += 1;
        }
        
        proof {
            assert(arr@.take((i + 1) as int) == arr@.take(i as int).push(arr[i as int]));
            /* code modified by LLM (iteration 1): add explicit type annotations for integer literals */
            assert(count_frequency_rcr(arr@.take((i + 1) as int), key) == 
                   count_frequency_rcr(arr@.take(i as int), key) + 
                   if arr[i as int] == key { 1int } else { 0int });
        }
        
        i += 1;
    }
    
    proof {
        assert(arr@.take(i as int) == arr@);
    }
    count
}

fn first_repeated_char(str1: &[u8]) -> (repeated_char: Option<(usize, u8)>)
    ensures
        if let Some((idx, rp_char)) = repeated_char {
            idx < str1.len() && str1[idx as int] == rp_char && count_frequency_rcr(str1@, rp_char) > 1 &&
            forall|k: int| 0 <= k < idx ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1
        } else {
            forall|k: int|
                0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1
        },
{
    let input_len = str1.len();
    proof {
        assert(str1@.take(0int).filter(|x: u8| count_frequency_rcr(str1@, x) > 1) == Seq::<
            u8,
        >::empty());
    }
    let mut index = 0;
    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            str1@.take(index as int) =~= str1@.take(index as int).filter(
                |x: u8| count_frequency_rcr(str1@, x) <= 1,
            ),
    {
        /* code modified by LLM (iteration 1): use usize indexing instead of int cast */
        if count_frequency(&str1, str1[index]) > 1 {
            return Some((index, str1[index]));
        }
        proof {
            assert(str1@.take((index + 1) as int).drop_last() == str1@.take(index as int));
            reveal(Seq::filter);
        }
        index += 1;
    }
    proof {
        assert(str1@ =~= str1@.take(input_len as int));
        assert(forall|k: int|
            0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1);
    }
    None
}

} // verus!