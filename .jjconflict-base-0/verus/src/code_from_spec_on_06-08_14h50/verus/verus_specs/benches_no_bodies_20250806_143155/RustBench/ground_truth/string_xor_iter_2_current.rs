use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn xor_strings(a: Vec<char>, b: Vec<char>) -> (result: Vec<char>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> (a[i] == '0' || a[i] == '1'),
        forall|i: int| 0 <= i && i < b.len() ==> (b[i] == '0' || b[i] == '1')
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if a[i] == b[i] { '0' } else { '1' })
{
    let mut result: Vec<char> = Vec::new();
    let mut i = 0;
    /* code modified by LLM (iteration 1): Added decreases clause to fix verification error */
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == (if a[j] == b[j] { '0' } else { '1' })
        decreases a.len() - i
    {
        let bit = if a[i] == b[i] { '0' } else { '1' };
        result.push(bit);
        i += 1;
    }
    result
}

fn main() {}
}