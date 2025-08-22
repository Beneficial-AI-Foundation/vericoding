use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
        forall|i: int| #![auto] 0 <= i && i < result.len() ==> result[i] == (if i < a.len() { a[i] } else { b }),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[j],
    {
        result.push(a[i]);
        i = i + 1;
    }
    result.push(b);
    result
}

fn main() {}
}
