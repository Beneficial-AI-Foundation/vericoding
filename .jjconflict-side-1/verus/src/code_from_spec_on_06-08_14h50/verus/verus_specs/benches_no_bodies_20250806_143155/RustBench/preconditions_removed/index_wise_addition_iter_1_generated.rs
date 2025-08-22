use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn index_wise_addition(a: &Vec<Vec<i32>>, b: &Vec<Vec<i32>>) -> (c: Vec<Vec<i32>>)
    ensures
        c.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < c.len() ==> c[i].len() == a[i].len(),
        forall|i: int| #![trigger a[i], b[i], c[i]]
            0 <= i < c.len()
                ==> forall|j: int| #![auto] 0 <= j < c[i].len() ==> c[i][j] == a[i][j] + b[i][j],
{
    let mut c = Vec::new();
    
    for i in 0..a.len()
        invariant
            c.len() == i,
            forall|k: int| #![auto] 0 <= k < c.len() ==> c[k].len() == a[k].len(),
            forall|k: int| #![trigger a[k], b[k], c[k]]
                0 <= k < c.len()
                    ==> forall|j: int| #![auto] 0 <= j < c[k].len() ==> c[k][j] == a[k][j] + b[k][j],
    {
        let mut row = Vec::new();
        
        for j in 0..a[i].len()
            invariant
                row.len() == j,
                forall|l: int| #![auto] 0 <= l < row.len() ==> row[l] == a[i][l] + b[i][l],
        {
            row.push(a[i][j] + b[i][j]);
        }
        
        c.push(row);
    }
    
    c
}

fn main() {}
}