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
/* helper modified by LLM (iteration 5): fixed index_of usage by properly using forall instead of option matching */
fn lemma_max_element_in_subrange(l: Seq<int>, start: int, end: int, max_val: int)
    requires
        0 <= start < end <= l.len(),
        is_max_element(l.subrange(start, end), max_val),
    ensures
        l.contains(max_val),
        forall|i: int| start <= i < end ==> l[i] <= max_val,
{
    proof {
        let sub = l.subrange(start, end);
        assert(sub.contains(max_val));
        assert forall|i: int| start <= i < end implies l[i] <= max_val by {
            assert(sub[i - start] == l[i]);
            assert(sub[i - start] <= max_val);
        }
        assert(l.contains(max_val)) by {
            assert forall|i: int| 0 <= i < sub.len() implies l[start + i] == sub[i];
            let idx = sub.index_of(max_val);
            assert(l[start + idx] == max_val);
        }
    }
}

fn lemma_max_extends(l: Seq<int>, current_max: int, new_element: int)
    requires
        l.len() > 0,
        is_max_element(l, current_max),
    ensures
        is_max_element(l.push(new_element), if new_element > current_max { new_element } else { current_max }),
{
    proof {
        let extended = l.push(new_element);
        let new_max = if new_element > current_max { new_element } else { current_max };
        assert(extended.contains(new_max));
        assert forall|i: int| 0 <= i < extended.len() implies extended[i] <= new_max by {
            if i < l.len() {
                assert(extended[i] == l[i]);
                assert(l[i] <= current_max);
            } else {
                assert(extended[i] == new_element);
            }
        }
    }
}

fn lemma_single_element_max(l: Seq<int>)
    requires l.len() == 1
    ensures is_max_element(l, l[0])
{
    proof {
        assert(l.contains(l[0]));
        assert forall|i: int| 0 <= i < l.len() implies l[i] <= l[0] by {
            assert(i == 0);
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
    /* code modified by LLM (iteration 5): simplified to handle the base case properly */
    let mut max_val = l[0];
    
    if l.len() == 1 {
        return max_val;
    }
    
    let mut i = 1;
    
    while i < l.len()
        invariant
            1 <= i <= l.len(),
            is_max_element(l@.subrange(0, i as int).map(|j, x| x as int), max_val as int),
        decreases l.len() - i
    {
        if l[i] > max_val {
            max_val = l[i];
        }
        i += 1;
    }
    
    max_val
}
// </vc-code>


}

fn main() {}