use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn filter_append_lemma<T>(s1: Seq<T>, s2: Seq<T>, pred: spec_fn(T) -> bool)
    ensures s1.add(s2).filter(pred) == s1.filter(pred).add(s2.filter(pred))
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1.add(s2) == s2);
        assert(s1.filter(pred) == Seq::<T>::empty());
    } else {
        let s1_first = s1[0];
        let s1_rest = s1.subrange(1, s1.len() as int);
        assert(s1 == seq![s1_first].add(s1_rest));
        
        filter_append_lemma(s1_rest, s2, pred);
        
        assert(s1.add(s2) == seq![s1_first].add(s1_rest.add(s2)));
        assert((seq![s1_first].add(s1_rest.add(s2))).filter(pred) == 
               seq![s1_first].filter(pred).add((s1_rest.add(s2)).filter(pred)));
        assert((s1_rest.add(s2)).filter(pred) == s1_rest.filter(pred).add(s2.filter(pred)));
        assert(s1.filter(pred) == seq![s1_first].filter(pred).add(s1_rest.filter(pred)));
    }
}

proof fn subrange_filter_extension_lemma(arr: Seq<u32>, i: int)
    requires 0 <= i < arr.len()
    ensures 
        arr.subrange(0, i + 1).filter(|x: u32| x % 2 != 0) ==
        arr.subrange(0, i).filter(|x: u32| x % 2 != 0).add(
            if arr[i] % 2 != 0 { seq![arr[i]] } else { seq![] }
        )
{
    let prefix = arr.subrange(0, i);
    let elem = arr[i];
    let extended = arr.subrange(0, i + 1);
    
    assert(extended == prefix.add(seq![elem]));
    filter_append_lemma(prefix, seq![elem], |x: u32| x % 2 != 0);
    
    if elem % 2 != 0 {
        assert(seq![elem].filter(|x: u32| x % 2 != 0) == seq![elem]);
    } else {
        /* code modified by LLM (iteration 5): fixed type annotation for empty sequence comparison */
        assert(seq![elem].filter(|x: u32| x % 2 != 0) =~= Seq::<u32>::empty());
    }
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    
    /* code modified by LLM (iteration 3): added proof block to establish invariant maintenance */
    while i < arr.len()
        invariant
            i <= arr.len(),
            odd_list@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 3): added proof to help verification */
        proof {
            subrange_filter_extension_lemma(arr@, i as int);
        }
        
        if arr[i] % 2 != 0 {
            odd_list.push(arr[i]);
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 3): added proof to establish postcondition */
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    odd_list
}
// </vc-code>

} // verus!

fn main() {}