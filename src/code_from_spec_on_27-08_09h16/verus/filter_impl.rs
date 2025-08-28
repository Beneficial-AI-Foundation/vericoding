use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn filter_property_push<T>(s: Seq<T>, elem: T, pred: spec_fn(T) -> bool) -> bool {
    if pred(elem) {
        s.filter(pred).push(elem) == s.push(elem).filter(pred)
    } else {
        s.filter(pred) == s.push(elem).filter(pred)
    }
}

proof fn lemma_filter_push<T>(s: Seq<T>, elem: T, pred: spec_fn(T) -> bool)
    ensures filter_property_push(s, elem, pred)
{
    if pred(elem) {
        let filtered_s = s.filter(pred);
        let s_with_elem = s.push(elem);
        let filtered_s_with_elem = s_with_elem.filter(pred);
        
        assert(filtered_s_with_elem.len() == filtered_s.len() + 1);
        assert(forall |i: int| 0 <= i < filtered_s.len() ==> 
            filtered_s[i] == filtered_s_with_elem[i]);
        assert(filtered_s_with_elem[filtered_s_with_elem.len() - 1] == elem);
    } else {
        let filtered_s = s.filter(pred);
        let s_with_elem = s.push(elem);
        let filtered_s_with_elem = s_with_elem.filter(pred);
        
        assert(filtered_s_with_elem.len() == filtered_s.len());
        assert(forall |i: int| 0 <= i < filtered_s.len() ==> 
            filtered_s[i] == filtered_s_with_elem[i]);
    }
}
// </vc-helpers>

// <vc-spec>
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    // pre-conditions-start
    requires 
        old(y).len() == 0,
    // pre-conditions-end
    // post-conditions-start
    ensures 
        y@ == x@.filter(|k:u64| k%3 == 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    for i in 0..x.len()
        invariant
            y.len() <= i,
            y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0),
    {
        let elem = x[i];
        if elem % 3 == 0 {
            y.push(elem);
        }
        proof {
            let current_subrange = x@.subrange(0, i as int);
            let next_subrange = x@.subrange(0, (i + 1) as int);
            let current_elem = x@[i as int];
            
            assert(next_subrange == current_subrange.push(current_elem));
            lemma_filter_push(current_subrange, current_elem, |k:u64| k%3 == 0);
            
            if current_elem % 3 == 0 {
                assert(filter_property_push(current_subrange, current_elem, |k:u64| k%3 == 0));
                assert(current_subrange.filter(|k:u64| k%3 == 0).push(current_elem) == 
                       next_subrange.filter(|k:u64| k%3 == 0));
            } else {
                assert(filter_property_push(current_subrange, current_elem, |k:u64| k%3 == 0));
                assert(current_subrange.filter(|k:u64| k%3 == 0) == 
                       next_subrange.filter(|k:u64| k%3 == 0));
            }
        }
    }
}
// </vc-code>

}

fn main() {}