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
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            count == count_frequency_rcr(arr@.take(i as int), key),
            /* code modified by LLM (iteration 1): added bounds invariant to prevent overflow */
            count <= i,
        decreases arr.len() - i,
    {
        if arr[i] == key {
            /* code modified by LLM (iteration 1): added overflow check */
            assert(count < arr.len()); // This ensures no overflow since count <= i < arr.len()
            count = count + 1;
        }
        i = i + 1;
        
        /* code modified by LLM (iteration 2): fixed type annotation for literals */
        assert(count_frequency_rcr(arr@.take(i as int), key) == 
               count_frequency_rcr(arr@.take((i-1) as int), key) + 
               if arr@[(i-1) as int] == key { 1int } else { 0int });
    }
    
    assert(arr@.take(arr.len() as int) =~= arr@);
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
    
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|k: int| 0 <= k < i ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1,
        decreases str1.len() - i,
    {
        let freq = count_frequency(str1, str1[i]);
        if freq > 1 {
            /* code modified by LLM (iteration 1): added lemma to prove filter equality */
            assert(forall|x: char| str1@.take(i as int).contains(x) ==> count_frequency_rcr(str1@, x) <= 1);
            assert(forall|x: char| str1@.take(i as int).contains(x) ==> 
                   count_frequency_rcr(str1@, x) <= 1 <==> true);
            
            /* code modified by LLM (iteration 1): prove that filter doesn't change the sequence */
            assert(str1@.take(i as int).filter(|x: char| count_frequency_rcr(str1@, x) <= 1) 
                   =~= str1@.take(i as int));
            
            return Some((i, str1[i]));
        }
        i = i + 1;
    }
    
    None
}

} // verus!

fn main() {}