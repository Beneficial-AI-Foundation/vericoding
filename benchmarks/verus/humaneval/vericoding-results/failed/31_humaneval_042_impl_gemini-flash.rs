// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(l: Seq<int>) -> bool
{
    true
}

spec fn correct_output(l: Seq<int>, result: Seq<int>) -> bool
{
    result.len() == l.len() && 
    forall|i: int| 0 <= i < l.len() ==> result[i] == l[i] + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed the empty helper block */
// </vc-helpers>

// <vc-spec>
fn incr_list(l: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(l@.map(|i: int, x: i8| x as int))
    ensures correct_output(l@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed the invariant to `forall|j: int| 0 <= j < i ==> result_vec@[j] == (l@[j] + 1). Also fixed the type casting issues. */
{
    let mut result_vec: Vec<i8> = Vec::new();
    let mut i: nat = 0;

    while (i as int) < (l.len() as int)
        invariant
            0 <= i,
            i <= l.len(),
            result_vec.len() == i,
            forall|j: nat| j < i ==> result_vec@[j] == (l@[j] + 1),
        decreases (l.len() as int) - (i as int)
    {
        let val: i8 = l@[i];
        result_vec.push(val + 1);
        i = i + 1;
    }
    
    result_vec
}
// </vc-code>


}

fn main() {}