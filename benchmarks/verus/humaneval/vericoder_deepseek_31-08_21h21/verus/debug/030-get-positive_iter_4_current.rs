use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn positive_filter(s: Seq<i32>) -> Seq<i32> {
    s.filter(|x: i32| x > 0)
}

proof fn filter_len_property<T>(s: Seq<T>, f: spec_fn(T) -> bool) 
    decreases s.len()
    ensures
        s.filter(f).len() <= s.len(),
{
    if s.len() == 0 {
        return;
    }
    let sub = s.subrange(0, s.len() as int - 1);
    filter_len_property(sub, f);
}

proof fn filter_index_property(s: Seq<i32>) 
    ensures
        forall|i: int| 0 <= i < s.filter(|x: i32| x > 0).len() ==> 
            s.filter(|x: i32| x > 0).index(i) > 0,
{
    assert forall|i: int| 0 <= i < s.filter(|x: i32| x > 0).len() implies 
        s.filter(|x: i32| x > 0).index(i) > 0 by {
        let filtered = s.filter(|x: i32| x > 0);
        assert(filtered.index(i) > 0);
    };
}

proof fn filter_membership_property(s: Seq<i32>, elem: i32)
    ensures
        elem > 0 && s.contains(elem) ==> s.filter(|x: i32| x > 0).contains(elem),
{
    if elem > 0 && s.contains(elem) {
        assert(s.filter(|x: i32| x > 0).contains(elem));
    }
}

proof fn filter_subrange_equivalence(s: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        s.subrange(start, end).filter(|x: i32| x > 0) == s.filter(|x: i32| x > 0).subrange(
            s.filter(|x: i32| x > 0).num_elements(|i| s.index(i) > 0 && i < start) as int,
            s.filter(|x: i32| x > 0).num_elements(|i| s.index(i) > 0 && i < end) as int
        ),
{
}

proof fn filter_append_property(s1: Seq<i32>, s2: Seq<i32>)
    ensures
        s1.add(s2).filter(|x: i32| x > 0) == s1.filter(|x: i32| x > 0).add(s2.filter(|x: i32| x > 0)),
{
}
// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    // post-conditions-start
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut positive_list = Vec::new();
    let mut index: usize = 0;
    
    while index < input.len()
        invariant
            positive_list@ == input@.subrange(0, index as int).filter(|x: i32| x > 0),
            index <= input.len(),
    {
        let elem = input[index];
        if elem > 0 {
            positive_list.push(elem);
        }
        index = index + 1;
    }
    
    proof {
        assert(positive_list@ == input@.filter(|x: i32| x > 0));
    }
    
    positive_list
}
// </vc-code>

fn main() {}
}