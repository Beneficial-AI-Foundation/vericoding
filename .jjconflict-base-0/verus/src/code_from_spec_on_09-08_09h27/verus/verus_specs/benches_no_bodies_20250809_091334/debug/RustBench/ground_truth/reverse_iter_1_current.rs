use vstd::prelude::*;

verus! {

fn reverse(a: &[i32]) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
{
    let mut result = Vec::new();
    let mut j = a.len();
    
    while j > 0
        invariant
            result.len() == a.len() - j,
            forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
    {
        j = j - 1;
        result.push(a[j]);
    }
    
    result
}

fn main() {}
}