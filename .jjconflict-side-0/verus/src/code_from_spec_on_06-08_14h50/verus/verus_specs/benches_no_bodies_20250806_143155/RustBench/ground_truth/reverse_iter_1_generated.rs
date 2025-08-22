use vstd::prelude::*;

verus! {

fn reverse(a: &[i32]) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
{
    let mut result = Vec::new();
    let mut i = a.len();
    
    while i > 0
        invariant
            result.len() == a.len() - i,
            forall|j: int| 0 <= j && j < result.len() ==> result[j] == a[a.len() - 1 - j],
    {
        i = i - 1;
        result.push(a[i]);
    }
    
    result
}

fn main() {}
}