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

proof fn filter_push_lemma(seq: Seq<i32>, x: i32, p: spec_fn(i32) -> bool)
    ensures
        seq.push(x).filter(p) == seq.filter(p) + if p(x) { seq![x] } else { seq![] },
{
    assert(seq.push(x) == seq + seq![x]);
    
    if p(x) {
        assert(seq![x].filter(p) == seq![x]);
        assert((seq + seq![x]).filter(p) == seq.filter(p) + seq![x].filter(p)) by {
            let predicate = p;
            seq_filter_distributes(seq, seq![x], predicate);
        };
        assert(seq.filter(p) + seq![x].filter(p) == seq.filter(p) + seq![x]);
    } else {
        assert(seq![x].filter(p) == seq![]);
        assert((seq + seq![x]).filter(p) == seq.filter(p) + seq![x].filter(p)) by {
            let predicate = p;
            seq_filter_distributes(seq, seq![x], predicate);
        };
        assert(seq.filter(p) + seq![x].filter(p) == seq.filter(p) + seq![]);
        assert(seq.filter(p) + seq![] == seq.filter(p));
    }
}

proof fn seq_filter_distributes<T>(s1: Seq<T>, s2: Seq<T>, p: spec_fn(T) -> bool)
    ensures
        (s1 + s2).filter(p) == s1.filter(p) + s2.filter(p),
    decreases s2.len(),
{
    if s2.len() == 0 {
        assert(s1 + s2 == s1);
        assert(s2.filter(p) == seq![]);
    } else {
        let s2_init = s2.drop_last();
        let last_elem = s2.last();
        assert(s2 == s2_init.push(last_elem));
        
        seq_filter_distributes(s1, s2_init, p);
        
        assert((s1 + s2).filter(p) == (s1 + s2_init + seq![last_elem]).filter(p));
        assert((s1 + s2_init + seq![last_elem]).filter(p) == 
               (s1 + s2_init).filter(p) + seq![last_elem].filter(p));
        
        if p(last_elem) {
            assert(seq![last_elem].filter(p) == seq![last_elem]);
            assert(s2.filter(p) == s2_init.filter(p).push(last_elem));
        } else {
            assert(seq![last_elem].filter(p) == seq![]);
            assert(s2.filter(p) == s2_init.filter(p));
        }
    }
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
    let mut unique_arr = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            unique_arr@ == arr@.subrange(0, i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
        decreases arr.len() - i,
    {
        let freq = count_frequency(arr, arr[i]);
        if freq == 1 {
            unique_arr.push(arr[i]);
        }
        i += 1;
        
        proof {
            let prev_seq = arr@.subrange(0, i - 1 as int);
            let curr_elem = arr@[i - 1];
            
            assert(arr@.subrange(0, i as int) == prev_seq.push(curr_elem));
            
            filter_push_lemma(prev_seq, curr_elem, |x: i32| count_frequency_rcr(arr@, x) == 1);
            
            if count_frequency_rcr(arr@, curr_elem) == 1 {
                assert(prev_seq.filter(|x: i32| count_frequency_rcr(arr@, x) == 1).push(curr_elem) == 
                       prev_seq.push(curr_elem).filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
            } else {
                assert(prev_seq.filter(|x: i32| count_frequency_rcr(arr@, x) == 1) == 
                       prev_seq.push(curr_elem).filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
            }
        }
    }
    
    proof {
        assert(arr@ == arr@.subrange(0, i as int));
    }
    
    unique_arr
}
// </vc-code>

} // verus!

fn main() {}