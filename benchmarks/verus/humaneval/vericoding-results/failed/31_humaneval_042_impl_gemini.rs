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
/* helper modified by LLM (iteration 5): removed redefinition of valid_input to fix compilation error */
// </vc-helpers>

// <vc-spec>
fn incr_list(l: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(l@.map(|i: int, x: i8| x as int))
    ensures correct_output(l@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented a standard loop; verification requires a precondition that rules out i8 overflow */
    let mut result = l.clone();
    let mut i: usize = 0;
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            result.len() == l.len(),
            forall|j: int| 0 <= j < i ==> result@[j] as int == l@[j] as int + 1,
            forall|j: int| i <= j < l.len() ==> result@[j] == l@[j],
        decreases l.len() - i
    {
        let val = l[i];
        // The verifier requires a precondition to prove `val < 127`
        // to ensure the following addition does not overflow.
        let new_val = val + 1;
        result.set(i, new_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}