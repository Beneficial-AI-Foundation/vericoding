use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    requires
        0 <= pos < a.len(),
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            0 <= pos < a.len(),
            result.len() == if i <= pos { i } else { i - 1 },
            forall|j: int| 0 <= j < pos && j < i ==> result[j] == a[j],
            forall|j: int| pos <= j < i - 1 ==> result[j] == a[j + 1],
    {
        if i != pos {
            result.push(a[i]);
        }
        i += 1;
    }
    
    result
}

fn main() {}
}