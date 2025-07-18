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
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    /* code modified by LLM (iteration 4): Fixed invariant and overflow issues */
    let mut count: usize = 0;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            count_frequency_rcr(arr@.take(i as int), key) == count as int,
            count <= i,
        decreases arr.len() - i,
    {
        if arr[i] == key {
            count += 1;
        }
        i += 1;
    }
    
    assert(arr@.take(i as int) == arr@);
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
    ensures
        check_first_repeated_char(str1, repeated_char),
{
    /* code modified by LLM (iteration 4): Fixed by using ghost variable for int conversion */
    let mut i = 0;
    
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1,
        decreases str1.len() - i,
    {
        let freq = count_frequency(str1, str1[i]);
        if freq > 1 {
            /* code modified by LLM (iteration 4): Use ghost variable for int conversion */
            let ghost i_ghost: int = i as int;
            let seq = str1@.take(i_ghost);
            let filtered = seq.filter(|x: char| count_frequency_rcr(str1@, x) <= 1);
            
            assert forall|j: int| 0 <= j < seq.len() implies count_frequency_rcr(str1@, seq[j]) <= 1 by {
                assert(seq[j] == str1@[j]);
                assert(0 <= j < i);
            }
            
            assert forall|j: int| 0 <= j < seq.len() implies filtered.contains(seq[j]) by {
                assert(count_frequency_rcr(str1@, seq[j]) <= 1);
            }
            
            assert forall|x: char| filtered.contains(x) implies seq.contains(x) by {}
            
            assert(seq.len() == filtered.len());
            assert forall|j: int| 0 <= j < seq.len() implies seq[j] == filtered[j] by {}
            assert(seq =~= filtered);
            
            return Some((i, str1[i]));
        }
        i += 1;
    }
    
    None
}

} // verus!

fn main() {}