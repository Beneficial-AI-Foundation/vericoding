use vstd::prelude::*;

verus! {

spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> (result: int)
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

// <vc-helpers>
fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= counter <= index,
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
        decreases arr.len() - index,
    {
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;
        assert(arr@.subrange(0, index - 1 as int) == arr@.subrange(0, index as int).drop_last());
    }
    assert(arr@ == arr@.subrange(0, index as int));
    counter
}

proof fn lemma_filter_properties(arr: Seq<i32>)
    ensures
        forall|x: i32| arr.filter(|y: i32| count_frequency_rcr(arr, y) == 1).contains(x) <==> 
               (arr.contains(x) && count_frequency_rcr(arr, x) == 1)
{
}

proof fn lemma_unique_elements_correspondence(arr: Seq<i32>, unique_arr: Seq<i32>)
    requires
        forall|j: int| 0 <= j < unique_arr.len() ==> count_frequency_rcr(arr, unique_arr[j]) == 1,
        forall|j: int| 0 <= j < arr.len() ==> (count_frequency_rcr(arr, arr[j]) == 1 <==> 
               exists|k: int| 0 <= k < unique_arr.len() && unique_arr[k] == arr[j]),
    ensures
        unique_arr =~= arr.filter(|x: i32| count_frequency_rcr(arr, x) == 1)
{
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    // post-conditions-start
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut unique_arr: Vec<i32> = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 5): fixed proof function syntax */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < unique_arr@.len() ==> count_frequency_rcr(arr@, unique_arr@[j]) == 1,
            forall|j: int| 0 <= j < i ==> (count_frequency_rcr(arr@, arr@[j]) == 1 <==> exists|k: int| 0 <= k < unique_arr@.len() && unique_arr@[k] == arr@[j]),
            forall|j: int, k: int| 0 <= j < k < unique_arr@.len() ==> unique_arr@[j] != unique_arr@[k],
        decreases arr.len() - i,
    {
        let freq = count_frequency(arr, arr[i]);
        if freq == 1 {
            proof {
                assert(count_frequency_rcr(arr@, arr[i as int]) == 1);
                assert(forall|k: int| 0 <= k < unique_arr@.len() ==> unique_arr@[k] != arr[i as int]);
            }
            unique_arr.push(arr[i]);
        }
        
        proof {
            assert(forall|j: int| 0 <= j < i + 1 ==> (count_frequency_rcr(arr@, arr@[j]) == 1 <==> 
                   exists|k: int| 0 <= k < unique_arr@.len() && unique_arr@[k] == arr@[j]));
        }
        
        i += 1;
    }
    
    proof {
        lemma_filter_properties(arr@);
        lemma_unique_elements_correspondence(arr@, unique_arr@);
    }
    
    unique_arr
}
// </vc-code>

} // verus!

fn main() {}