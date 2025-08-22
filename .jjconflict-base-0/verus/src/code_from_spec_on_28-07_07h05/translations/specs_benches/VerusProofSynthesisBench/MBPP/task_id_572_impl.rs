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

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    // post-conditions-start
    ensures
        count_frequency_rcr(arr@, key) == frequency,
    // post-conditions-end
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            count == count_frequency_rcr(arr@.take(i as int), key),
            /* code modified by LLM (iteration 1): added bound to prevent overflow */
            count <= i,
        decreases arr.len() - i,
    {
        if arr[i] == key {
            /* code modified by LLM (iteration 1): added overflow check and assertion */
            assert(count < usize::MAX);
            count = count + 1;
        }
        i = i + 1;
        
        /* code modified by LLM (iteration 2): moved lemma call into proof block */
        proof {
            lemma_count_frequency_take_extend(arr@, key, i as int);
        }
    }
    
    assert(arr@.take(arr.len() as int) == arr@);
    count
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    // post-conditions-start
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.take(i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
        decreases arr.len() - i,
    {
        let freq = count_frequency(arr, arr[i]);
        if freq == 1 {
            result.push(arr[i]);
        }
        i = i + 1;
        
        /* code modified by LLM (iteration 2): moved lemma call into proof block */
        proof {
            lemma_filter_take_extend(arr@, i as int);
        }
    }
    
    assert(arr@.take(arr.len() as int) == arr@);
    result
}

/* code modified by LLM (iteration 1): added helper lemma for count_frequency invariant */
proof fn lemma_count_frequency_take_extend(seq: Seq<i32>, key: i32, i: int)
    requires i >= 0, i <= seq.len()
    ensures 
        i > 0 ==> count_frequency_rcr(seq.take(i), key) == 
                  count_frequency_rcr(seq.take(i-1), key) + 
                  /* code modified by LLM (iteration 3): fixed type annotation for integer literal */
                  if seq[i-1] == key { 1int } else { 0int }
{
    if i > 0 {
        let taken = seq.take(i);
        let prev_taken = seq.take(i-1);
        
        assert(taken == prev_taken.push(seq[i-1]));
        lemma_count_frequency_push(prev_taken, seq[i-1], key);
    }
}

/* code modified by LLM (iteration 1): added helper lemma for push operation */
proof fn lemma_count_frequency_push(seq: Seq<i32>, elem: i32, key: i32)
    ensures count_frequency_rcr(seq.push(elem), key) == 
            /* code modified by LLM (iteration 3): fixed type annotation for integer literal */
            count_frequency_rcr(seq, key) + if elem == key { 1int } else { 0int }
{
    let extended = seq.push(elem);
    
    if extended.len() == 0 {
        // Base case - empty sequence
    } else {
        assert(extended.last() == elem);
        assert(extended.drop_last() == seq);
    }
}

/* code modified by LLM (iteration 1): added helper lemma for filter invariant */
proof fn lemma_filter_take_extend(seq: Seq<i32>, i: int)
    requires i >= 0, i <= seq.len()
    ensures 
        i > 0 ==> seq.take(i).filter(|x: i32| count_frequency_rcr(seq, x) == 1) ==
                  seq.take(i-1).filter(|x: i32| count_frequency_rcr(seq, x) == 1) +
                  if count_frequency_rcr(seq, seq[i-1]) == 1 { 
                      seq![seq[i-1]] 
                  } else { 
                      seq![] 
                  }
{
    if i > 0 {
        let taken = seq.take(i);
        let prev_taken = seq.take(i-1);
        let elem = seq[i-1];
        
        assert(taken == prev_taken.push(elem));
        
        // The filter property follows from the definition
        assert(forall |x: i32| taken.contains(x) <==> 
               (prev_taken.contains(x) || x == elem));
    }
}

} // verus!

fn main() {}