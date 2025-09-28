// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(l: Seq<int>) -> bool {
    l.len() > 0
}

spec fn is_max_element(l: Seq<int>, max_val: int) -> bool {
    l.contains(max_val) && forall|i: int| 0 <= i < l.len() ==> l[i] <= max_val
}

spec fn max_element_func(l: Seq<int>) -> int
    decreases l.len()
{
    if l.len() == 1 {
        l[0]
    } else if l.len() > 1 {
        let rest_max = max_element_func(l.subrange(1, l.len() as int));
        if l[0] > rest_max { l[0] } else { rest_max }
    } else {
        0int
    }
}

// </vc-preamble>

// <vc-helpers>
proof fn lemma_max_element_func_is_max(l: Seq<int>)
    requires l.len() > 0
    ensures is_max_element(l, max_element_func(l))
    decreases l.len()
{
    if l.len() == 1 {
        assert(l.contains(l[0]));
        assert(forall|i: int| 0 <= i < l.len() ==> l[i] <= l[0]);
    } else {
        let rest = l.subrange(1, l.len() as int);
        lemma_max_element_func_is_max(rest);
        let rest_max = max_element_func(rest);
        
        assert(rest.contains(rest_max));
        assert(forall|i: int| 0 <= i < rest.len() ==> rest[i] <= rest_max);
        
        if l[0] > rest_max {
            assert(l.contains(l[0]));
            assert(forall|i: int| 0 <= i < l.len() ==> l[i] <= l[0]) by {
                assert(forall|i: int| 1 <= i < l.len() ==> l[i] == rest[i - 1]);
            }
        } else {
            assert(forall|i: int| 1 <= i < l.len() ==> l[i] == rest[i - 1]);
            assert(exists|j: int| 1 <= j < l.len() && l[j] == rest_max) by {
                let j = choose|j: int| 0 <= j < rest.len() && rest[j] == rest_max;
                assert(l[j + 1] == rest[j]);
            }
            assert(l.contains(rest_max));
            assert(forall|i: int| 0 <= i < l.len() ==> l[i] <= rest_max);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_max_element(l: Vec<i8>) -> (max_val: i8)
    requires valid_input(l@.map(|i, x| x as int))
    ensures is_max_element(l@.map(|i, x| x as int), max_val as int)
// </vc-spec>
// <vc-code>
{
    let mut max_val = l[0];
    let mut i: usize = 1;
    
    while i < l.len()
        invariant
            1 <= i <= l.len(),
            is_max_element(l@.map(|j, x| x as int).subrange(0, i as int), max_val as int),
    {
        if l[i] > max_val {
            max_val = l[i];
        }
        
        assert(l@.map(|j, x| x as int).subrange(0, (i + 1) as int).contains(max_val as int));
        assert(forall|j: int| 0 <= j < (i + 1) ==> l@.map(|k, x| x as int)[j] <= max_val as int) by {
            assert(forall|j: int| 0 <= j < i ==> l@.map(|k, x| x as int)[j] <= max_val as int);
            if l[i] as int <= max_val as int {
                assert(l@.map(|k, x| x as int)[i as int] <= max_val as int);
            }
        }
        
        i = i + 1;
    }
    
    assert(l@.map(|j, x| x as int).subrange(0, l.len() as int) =~= l@.map(|j, x| x as int));
    max_val
}
// </vc-code>


}

fn main() {}