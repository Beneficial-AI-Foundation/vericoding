use vstd::prelude::*;

verus! {

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
    /* code modified by LLM (iteration 1): added explicit type annotation for Vec::new() */
    let mut c: Vec<Vec<i32>> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            c.len() == i,
            i <= a.len(),
            forall|k: int| #![auto] 0 <= k < i ==> c[k].len() == a[k].len(),
            forall|k: int| #![trigger a[k], b[k], c[k]] 
                0 <= k < i 
                    ==> forall|j: int| #![auto] 0 <= j < c[k].len() ==> c[k][j] == a[k][j] + b[k][j],
    {
        /* code modified by LLM (iteration 1): added explicit type annotation for Vec::new() */
        let mut row: Vec<i32> = Vec::new();
        let mut j = 0;
        
        while j < a[i].len()
            invariant
                row.len() == j,
                /* code modified by LLM (iteration 1): converted usize to int for comparison */
                j <= a[i as int].len(),
                i < a.len(),
                /* code modified by LLM (iteration 1): converted usize indices to int for array access */
                forall|l: int| #![auto] 0 <= l < j ==> row[l] == a[i as int][l] + b[i as int][l],
        {
            /* code modified by LLM (iteration 1): converted usize to int for array indexing */
            row.push(a[i as int][j as int] + b[i as int][j as int]);
            j += 1;
        }
        
        c.push(row);
        i += 1;
    }
    
    c
}

fn main() {}
}