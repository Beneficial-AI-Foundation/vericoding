use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn positive_filter(s: Seq<i32>) -> Seq<i32> {
    s.filter(|x: i32| x > 0)
}

proof fn filter_len_property<T>(s: Seq<T>, f: spec_fn(T) -> bool) 
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
}

proof fn filter_membership_property(s: Seq<i32>, elem: i32)
    ensures
        elem > 0 && s.contains(elem) ==> s.filter(|x: i32| x > 0).contains(elem),
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
    assert(input@.len() >= 0);
    
    while index < input.len()
        invariant
            positive_list@ == input@.subrange(0, index as int).filter(|x: i32| x > 0),
            index <= input.len(),
    {
        let elem = input[index];
        if elem > 0 {
            positive_list.push(elem);
            proof {
                filter_membership_property(input@, elem);
            }
        }
        index = index + 1;
    }
    
    proof {
        filter_index_property(input@);
        assert(positive_list@ == input@.filter(|x: i32| x > 0));
    }
    
    positive_list
}
// </vc-code>

fn main() {}
}