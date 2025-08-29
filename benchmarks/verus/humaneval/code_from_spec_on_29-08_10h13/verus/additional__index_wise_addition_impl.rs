use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: "fn index_wise_addition(a: &Vec<Vec<i32>>, b: &Vec<Vec<i32>>) -> (c: Vec<Vec<i32>>)"
docstring: Add corresponding elements from two arrays element-wise.
*/
// </vc-description>

// <vc-spec>
fn index_wise_addition(a: &Vec<Vec<i32>>, b: &Vec<Vec<i32>>) -> (c: Vec<Vec<i32>>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a@[i].len() == b@[i].len()
    ensures
        c.len() == a.len(),
        forall|i: int| 0 <= i < c.len() ==> c@[i].len() == a@[i].len(),
        forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c@[i].len() ==> 
            c@[i]@[j] == a@[i]@[j] + b@[i]@[j]
// </vc-spec>

// <vc-code>
{
    /* code modified by LLM (iteration 5): added bounds assertions for array access */
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k].len() == a@[k].len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < result@[k].len() ==> 
                result@[k]@[j] == a@[k]@[j] + b@[k]@[j]
        decreases a.len() - i
    {
        let mut row = Vec::new();
        let mut j = 0;
        
        /* code modified by LLM (iteration 5): assert bounds for precondition requirements */
        assert(i < a.len());
        assert(i < b.len());
        assert(a@[i as int].len() == b@[i as int].len());
        
        while j < a[i].len()
            invariant
                i < a.len(),
                i < b.len(),
                j <= a@[i as int].len(),
                a@[i as int].len() == b@[i as int].len(),
                row.len() == j,
                forall|k: int| 0 <= k < j ==> row@[k] == a@[i as int]@[k] + b@[i as int]@[k]
            decreases a@[i as int].len() - j
        {
            /* code modified by LLM (iteration 5): assert bounds for indexing */
            assert(j < a[i].len());
            assert(j < b[i].len());
            row.push(a[i][j] + b[i][j]);
            j += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}