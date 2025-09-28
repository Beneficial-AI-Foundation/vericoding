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
/* helper modified by LLM (iteration 5): Fixed sequence indexing and subrange with proper nat types */
fn max_helper(seq: Seq<int>) -> (max_val: int)
    requires
        seq.len() > 0,
    ensures
        is_max_element(seq, max_val),
    decreases seq.len()
{
    if seq.len() == 1 {
        seq@[0]
    } else {
        let first = seq@[0];
        let rest_seq = seq.subrange(1, seq.len() as nat);
        let rest_max = max_helper(rest_seq);
        if first > rest_max {
            first
        } else {
            rest_max
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
/* code modified by LLM (iteration 5): Fixed type casting and sequence handling */
{
    let ghost seq = l@.map(|i, x| x as int);
    proof {
        assert(valid_input(seq));
    }
    let max_val_int = max_helper(seq);
    proof {
        assert(max_val_int >= -128);
        assert(max_val_int <= 127);
    }
    let max_val = if max_val_int < -128 {
        -128i8
    } else if max_val_int > 127 {
        127i8
    } else {
        max_val_int as i8
    };
    proof {
        assert(is_max_element(seq, max_val as int));
    }
    max_val
}
// </vc-code>


}

fn main() {}