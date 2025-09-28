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

// </vc-helpers>

// <vc-spec>
fn incr_list(l: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(l@.map(|i: int, x: i8| x as int))
    ensures correct_output(l@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{ /* code modified by LLM (iteration 3): removed ghost block and fixed invariant to use direct sequence indexing */
    let mut result_vec = Vec::with_capacity(l.len());
    for i in 0..l.len()
        invariant
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec@[j] as int == l@[j] as int + 1,
    {
        let x = l[i];
        result_vec.push(x + 1);
    }
    result_vec
}
// </vc-code>


}

fn main() {}