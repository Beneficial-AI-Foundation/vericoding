use vstd::prelude::*;

verus! {

//IMPL index_wise_addition
#[verifier::loop_isolation(false)]
fn index_wise_addition(a: &Vec<Vec<i32>>, b: &Vec<Vec<i32>>) -> (c: Vec<Vec<i32>>)
    // pre-conditions-start
    requires
        a.len() == b.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> a[i].len() == b[i].len(),
        forall|i: int| #![trigger a[i], b[i]]
            0 <= i < a.len()
                ==> forall|j: int| 0 <= j < a[i].len() ==> a[i][j] + b[i][j] <= i32::MAX,
        forall|i: int| #![trigger a[i], b[i]]
            0 <= i < a.len()
                ==> forall|j: int| 0 <= j < a[i].len() ==> a[i][j] + b[i][j] >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        c.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < c.len() ==> c[i].len() == a[i].len(),
        forall|i: int| #![trigger a[i], b[i], c[i]]
            0 <= i < c.len()
                ==> forall|j: int| #![auto] 0 <= j < c[i].len() ==> c[i][j] == a[i][j] + b[i][j],
    // post-conditions-end
{
    let mut c: Vec<Vec<i32>> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            c.len() == i,
            forall|k: int| 0 <= k < i ==> c[k].len() == a[k].len(),
            forall|k: int| 0 <= k < i ==> 
                forall|j: int| 0 <= j < c[k].len() ==> c[k][j] == a[k][j] + b[k][j],
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j = 0;
        
        while j < a[i].len()
            invariant
                /* code modified by LLM (iteration 1): Fix type consistency by using proper int casting */
                j <= a[i].len(),
                row.len() == j,
                /* code modified by LLM (iteration 1): Fix index type casting for ghost context */
                forall|l: int| 0 <= l < j as int ==> row[l] == a[i as int][l] + b[i as int][l],
        {
            row.push(a[i][j] + b[i][j]);
            j += 1;
        }
        
        c.push(row);
        i += 1;
    }
    
    c
}

fn main() {}
}