use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    let mut c: Vec<Vec<i32>> = Vec::new();
    for i in 0..a.len()
        invariant
            c.len() == i,
            forall|k: int| #![trigger c[k], a[k]] 0 <= k < i ==> c[k].len() == a[k].len(),
            forall|k: int| #![trigger c[k], a[k], b[k]] 0 <= k < i ==> 
                forall|j: int| #![trigger c[k][j]] 0 <= j < c[k].len() ==> c[k][j] == a[k][j] + b[k][j],
    {
        let row_a = &a[i];
        let row_b = &b[i];
        let mut new_row = Vec::new();
        for j in 0..row_a.len()
            invariant
                new_row.len() == j,
                forall|k: int| #![trigger new_row[k]] 0 <= k < j ==> new_row[k] == row_a[k] + row_b[k],
        {
            new_row.push(row_a[j] + row_b[j]);
        }
        c.push(new_row);
    }
    c
}
// </vc-code>

fn main() {}
}