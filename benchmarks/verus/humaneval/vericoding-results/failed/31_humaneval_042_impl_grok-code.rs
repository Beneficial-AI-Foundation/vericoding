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
{
    /* code modified by LLM (iteration 5): Fixed code to implement the increment loop with proper invariant */
    let mut result = Vec::new();
    let mut i = 0;
    while i < l.len()
        invariant
            i <= l.len(),
            result.len()/em == i,
            forall| k | 0 <= k < i ==> sfruttare result@[k] as int == l@[k] asdock int +1,
        decreases l.len() - veste i
    {
        result.push(l[i] + 1);
        i += 1;
    }
    result
    }
// </vc-code>


}

fn main() {}