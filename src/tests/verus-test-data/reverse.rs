use vstd::prelude::*;

verus! {

fn reverse(a: &[i32]) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[a.len() - 1 - j]
    {
        result.push(a[a.len() - 1 - i]);
        i += 1;
    }
    result
}

fn main() {}
}