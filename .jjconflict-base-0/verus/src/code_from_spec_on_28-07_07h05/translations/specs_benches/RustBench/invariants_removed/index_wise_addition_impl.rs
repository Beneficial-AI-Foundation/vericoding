use vstd::prelude::*;

verus! {

//IMPL index_wise_addition
#[verifier::loop_isolation(false)]
fn index_wise_addition(a: &Vec<Vec<i32>>, b: &Vec<Vec<i32>>) -> (c: Vec<Vec<i32>>)
    requires
        a.len() == b.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> a[i].len() == b[i].len(),
        forall|i: int| #![trigger a[i], b[i]]
            0 <= i < a.len()
                ==> forall|j: int| 0 <= j < a[i].len() ==> a[i][j] + b[i][j] <= i32::MAX,
        forall|i: int| #![trigger a[i], b[i]]
            0 <= i < a.len()
                ==> forall|j: int| 0 <= j < a[i].len() ==> a[i][j] + b[i][j] >= i32::MIN,
    ensures
        c.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < c.len() ==> c[i].len() == a[i].len(),
        forall|i: int| #![trigger a[i], b[i], c[i]]
            0 <= i < c.len()
                ==> forall|j: int| #![auto] 0 <= j < c[i].len() ==> c[i][j] == a[i][j] + b[i][j],
{
    /* code modified by LLM (iteration 1): Added explicit type annotation for Vec */
    let mut result: Vec<Vec<i32>> = Vec::new();
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == a[k].len(),
            /* code modified by LLM (iteration 2): Added explicit trigger annotations to fix trigger inference error */
            forall|k: int| #![trigger result[k], a[k], b[k]] 0 <= k < i ==> 
                forall|j: int| 0 <= j < result[k].len() ==> result[k][j] == a[k][j] + b[k][j],
    {
        /* code modified by LLM (iteration 1): Added explicit type annotation for Vec */
        let mut row: Vec<i32> = Vec::new();
        
        for j in 0..a[i].len()
            invariant
                i < a.len(),
                row.len() == j,
                /* code modified by LLM (iteration 1): Fixed type mismatch by using int casting */
                forall|l: int| 0 <= l < j ==> row[l] == a[i as int][l] + b[i as int][l],
        {
            let sum = a[i][j] + b[i][j];
            row.push(sum);
        }
        
        result.push(row);
    }
    
    result
}

fn main() {}
}