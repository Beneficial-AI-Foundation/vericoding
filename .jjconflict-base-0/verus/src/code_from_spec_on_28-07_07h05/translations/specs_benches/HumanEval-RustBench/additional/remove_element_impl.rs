use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        0 <= pos < a.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
    // post-conditions-end
{
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            /* code modified by LLM (iteration 1): Fixed type mismatch by casting usize to int in conditional expression */
            result.len() == if i <= pos { i as int } else { i as int - 1 },
            forall|j: int| 0 <= j < result.len() && j < pos ==> result[j] == a[j],
            forall|j: int| pos <= j < result.len() ==> result[j] == a[j + 1],
        /* code modified by LLM (iteration 1): Added decreases clause to prove loop termination */
        decreases a.len() - i
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