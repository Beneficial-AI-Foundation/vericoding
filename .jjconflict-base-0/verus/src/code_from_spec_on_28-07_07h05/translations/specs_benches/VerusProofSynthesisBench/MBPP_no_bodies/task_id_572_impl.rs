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

/* code modified by LLM (iteration 3): added lemma to prove relationship between subrange operations */
proof fn lemma_subrange_push_last(seq: Seq<i32>, i: int, key: i32)
    requires 0 < i <= seq.len()
    ensures seq.subrange(0, i) == seq.subrange(0, i-1).push(seq[i-1])
    ensures count_frequency_rcr(seq.subrange(0, i), key) == 
            count_frequency_rcr(seq.subrange(0, i-1), key) + 
            if seq[i-1] == key { 1int } else { 0int }
{
    let sub_i = seq.subrange(0, i);
    let sub_i_minus_1 = seq.subrange(0, i-1);
    
    assert(sub_i == sub_i_minus_1.push(seq[i-1]));
    
    // Prove the count_frequency_rcr relationship
    assert(sub_i.drop_last() == sub_i_minus_1);
    assert(sub_i.last() == seq[i-1]);
}

/* code modified by LLM (iteration 3): added lemma to prove filter property for sequences */
proof fn lemma_filter_push(seq: Seq<i32>, prefix: Seq<i32>, elem: i32, pred: spec_fn(i32) -> bool)
    requires seq == prefix.push(elem)
    ensures seq.filter(pred) == prefix.filter(pred) + 
            if pred(elem) { seq![elem] } else { seq![] }
{
    // This lemma helps prove the filter property when pushing an element
}

// pure-end

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
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
            count == count_frequency_rcr(arr@.subrange(0, i as int), key),
            count <= i,
        decreases arr.len() - i,
    {
        if arr[i] == key {
            assert(count < arr.len());
            count = count + 1;
        }
        i = i + 1;
        
        /* code modified by LLM (iteration 3): use lemma to prove the assertion */
        proof {
            lemma_subrange_push_last(arr@, i as int, key);
        }
    }
    
    assert(arr@.subrange(0, arr.len() as int) == arr@);
    count
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    // post-conditions-start
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
        decreases arr.len() - i,
    {
        let freq = count_frequency(arr, arr[i]);
        assert(freq == count_frequency_rcr(arr@, arr[i as int]));
        
        if freq == 1 {
            result.push(arr[i]);
        }
        i = i + 1;
        
        /* code modified by LLM (iteration 3): use lemmas to prove the filter assertion */
        proof {
            let sub_i = arr@.subrange(0, i as int);
            let sub_i_minus_1 = arr@.subrange(0, (i-1) as int);
            let elem = arr[i-1];
            let pred = |x: i32| count_frequency_rcr(arr@, x) == 1;
            
            assert(sub_i == sub_i_minus_1.push(elem));
            lemma_filter_push(sub_i, sub_i_minus_1, elem, pred);
        }
    }
    
    assert(arr@.subrange(0, arr.len() as int) == arr@);
    result
}

} // verus!

fn main() {}