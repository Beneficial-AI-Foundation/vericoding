use vstd::prelude::*;

verus! {

//IMPL remove_element
#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
{
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            pos < a.len(),
            /* code modified by LLM (iteration 2): strengthened invariant to track skipped elements */
            result.len() == i - (if i > pos { 1 } else { 0 }),
            /* code modified by LLM (iteration 2): simplified bounds for elements before pos */
            forall|j: int| 0 <= j < result.len() && j < pos as int ==> result[j] == a[j],
            /* code modified by LLM (iteration 2): ensured proper mapping for elements after pos */
            forall|j: int| pos as int <= j < result.len() ==> result[j] == a[j + 1],
        decreases a.len() - i
    {
        if i != pos {
            result.push(a[i]);
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 2): added intermediate assertion to help verification */
    assert(i == a.len());
    assert(result.len() == a.len() - 1);
    
    result
}

fn main() {}
}