use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if a[i] == b[i] { '0' } else { '1' })
{
    let mut result: Vec<char> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == (if a[j] == b[j] { '0' } else { '1' })
    {
        let bit = if a[i] == b[i] { '0' } else { '1' };
        result.push(bit);
        i += 1;
    }
    result
}

fn main() {}
}
