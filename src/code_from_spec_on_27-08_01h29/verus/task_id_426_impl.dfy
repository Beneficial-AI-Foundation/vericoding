use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn filter_push_lemma<T>(s: Seq<T>, elem: T, pred: spec_fn(T) -> bool) 
    ensures s.push(elem).filter(pred) == 
            if pred(elem) { s.filter(pred).push(elem) } else { s.filter(pred) }
{
    s.push(elem).filter(pred)
}

proof fn prove_filter_push<T>(s: Seq<T>, elem: T, pred: spec_fn(T) -> bool)
    ensures s.push(elem).filter(pred) == 
            if pred(elem) { s.filter(pred).push(elem) } else { s.filter(pred) }
{
    // This is provable by Verus automatically
}
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    // post-conditions-start
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut odd_list = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            odd_list@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i
    {
        if arr[i] % 2 != 0 {
            odd_list.push(arr[i]);
        }
        
        proof {
            let old_i = i as int;
            let new_i = (i + 1) as int;
            assert(arr@.subrange(0, new_i) == arr@.subrange(0, old_i).push(arr@[old_i]));
            
            prove_filter_push(arr@.subrange(0, old_i), arr@[old_i], |x: u32| x % 2 != 0);
            
            if arr@[old_i] % 2 != 0 {
                assert(arr@.subrange(0, new_i).filter(|x: u32| x % 2 != 0) == 
                       arr@.subrange(0, old_i).filter(|x: u32| x % 2 != 0).push(arr@[old_i]));
            } else {
                assert(arr@.subrange(0, new_i).filter(|x: u32| x % 2 != 0) == 
                       arr@.subrange(0, old_i).filter(|x: u32| x % 2 != 0));
            }
        }
        
        i += 1;
    }
    
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    odd_list
}
// </vc-code>

} // verus!

fn main() {}