// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn multiply(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == a[i] as int * b[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added opening brace, corrected invariant and ensures syntax, ensured proper Verus parsing */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i as int <= a.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == a@[j] * b@[j],
        decreases a.len() - i
    {
        let prod = (a@[i] as i32) * (b@[i] as i32);
        result.push(prod as i8);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}