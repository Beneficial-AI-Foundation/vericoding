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
/* helper modified by LLM (iteration 5): lemma that max_element_func returns a maximum element for non-empty seq */
proof fn max_element_func_proves_is_max(l: Seq<int>)
    requires
        valid_input(l),
    ensures
        is_max_element(l, max_element_func(l)),
    decreases
        l.len()
{
    if l.len() == 1 {
        assert(l.contains(l[0]));
        assert(forall|i: int| 0 <= i < l.len() as int ==> l[i] <= l[0]);
    } else {
        let rest = l.subrange(1, l.len() as int);
        max_element_func_proves_is_max(rest);
        let rest_max = max_element_func(rest);
        if l[0] > rest_max {
            assert(l.contains(l[0]));
            assert(forall|i: int| 0 <= i < l.len() as int ==>
                if i == 0 { l[i] <= l[0] } else { l[i] <= rest_max });
            assert(l[0] > rest_max);
            assert(forall|i: int| 0 <= i < l.len() as int ==> l[i] <= l[0]);
        } else {
            assert(is_max_element(rest, rest_max));
            assert(forall|k: int| 0 <= k < rest.len() as int ==> rest[k] == l[k + 1]);
            assert(exists|k: int| 0 <= k < rest.len() as int && rest[k] == rest_max);
            assert(exists|k: int| 0 <= k < l.len() as int && l[k] == rest_max);
            assert(l[0] <= rest_max);
            assert(forall|i: int| 0 <= i < l.len() as int ==> l[i] <= rest_max);
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
/* code modified by LLM (iteration 5): iterative scan using max_element_func on prefixes */
{
    let n = l.len();
    let mut i: usize = 1;
    let mut current_max: i8 = l[0];
    proof {
        let seq = l@.map(|k, x| x as int);
        max_element_func_proves_is_max(seq.subrange(0, 1));
        assert(max_element_func(seq.subrange(0, 1)) as int == current_max as int);
    }
    while i < n
        invariant
            1 <= i as int,
            i as int <= l@.len() as int,
            max_element_func(l@.map(|k, x| x as int).subrange(0, i as int)) as int == current_max as int,
        decreases
            (l@.len() as int) - i as int
    {
        let x = l[i];
        if x > current_max {
            current_max = x;
        }
        i = i + 1;
    }
    proof {
        let seq = l@.map(|k, x| x as int);
        max_element_func_proves_is_max(seq);
        assert(max_element_func(seq) as int == current_max as int);
    }
    current_max
}
// </vc-code>


}

fn main() {}