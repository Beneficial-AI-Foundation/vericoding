use vstd::prelude::*;

verus! {

spec fn count_frequency_rcr(seq: Seq<char>, key: char) -> (result: int)
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
// pure-end

fn count_frequency(arr: &Vec<char>, key: char) -> (frequency: usize)
    // post-conditions-start
    ensures
        count_frequency_rcr(arr@, key) == frequency,
    // post-conditions-end
{
    let mut count = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to while loop */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            count == count_frequency_rcr(arr@.take(i as int), key),
        decreases arr.len() - i,
    {
        if arr[i] == key {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(arr@.take(arr.len() as int) =~= arr@);
    }
    
    count
}

spec fn check_first_repeated_char(str1: &Vec<char>, repeated_char: Option<(usize, char)>) -> (res: bool) {
    if let Some((idx, rp_char)) = repeated_char {
        &&& str1@.take(idx as int) =~= str1@.take(idx as int).filter(
            |x: char| count_frequency_rcr(str1@, x) <= 1,
        )
        &&& count_frequency_rcr(str1@, rp_char) > 1
    } else {
        forall|k: int|
            0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1
    }
}
// pure-end

fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)
    // post-conditions-start
    ensures
        check_first_repeated_char(str1, repeated_char),
    // post-conditions-end
{
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to while loop */
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1,
        decreases str1.len() - i,
    {
        let freq = count_frequency(str1, str1[i]);
        if freq > 1 {
            proof {
                assert(str1@.take(i as int) =~= str1@.take(i as int).filter(
                    |x: char| count_frequency_rcr(str1@, x) <= 1,
                )) by {
                    assert forall|j: int| 0 <= j < i implies count_frequency_rcr(str1@, str1@[j]) <= 1 by {
                        assert(str1[j] == str1@[j]);
                    }
                }
            }
            return Some((i, str1[i]));
        }
        i = i + 1;
    }
    
    None
}

} // verus!

fn main() {}