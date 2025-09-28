// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(diameters: Seq<int>) -> bool {
    diameters.len() > 0 && forall|i: int| 0 <= i < diameters.len() ==> diameters[i] > 0
}

spec fn num_distinct(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.subrange(1, s.len() as int).contains(s[0]) {
        num_distinct(s.subrange(1, s.len() as int))
    } else {
        1 + num_distinct(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed mutability declarations for rest_vec */
fn count_distinct_helper(v: Vec<i8>, processed: Vec<i8>) -> (result: i8)
    requires
        valid_input(v@.map(|i, x| x as int)),
        forall|i: int| 0 <= i < processed@.len() ==> processed@[i] > 0,
    ensures
        result as int >= 1,
        result as int <= v@.len(),
    decreases v@.len()
{
    if v.len() == 0 {
        0
    } else {
        let first = v[0];
        let mut found = false;
        let mut i = 0;
        while i < processed.len()
            invariant
                0 <= i <= processed@.len(),
                found == processed@.subrange(0, i as int).contains(first),
        {
            if processed[i] == first {
                found = true;
                break;
            }
            i += 1;
        }
        
        let ghost rest = v@.subrange(1, v@.len() as int);
        if found {
            let mut rest_vec = v.clone();
            rest_vec.remove(0);
            count_distinct_helper(rest_vec, processed)
        } else {
            let mut new_processed = processed;
            new_processed.push(first);
            let mut rest_vec = v.clone();
            rest_vec.remove(0);
            1 + count_distinct_helper(rest_vec, new_processed)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(diameters: Vec<i8>) -> (result: i8)
    requires 
        valid_input(diameters@.map(|i, x| x as int)),
    ensures 
        result as int == num_distinct(diameters@.map(|i, x| x as int)),
        result as int >= 1,
        result as int <= diameters@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using fixed helper */
    let empty_vec: Vec<i8> = Vec::new();
    count_distinct_helper(diameters, empty_vec)
}
// </vc-code>


}

fn main() {}