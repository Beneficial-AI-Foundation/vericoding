// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatch in decreases clause */
    let mut c: Vec<Vec<i32>> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            c.len() == i,
            forall|k: int| #![auto] 0 <= k < i ==> c@[k].len() == a@[k].len(),
            forall|k: int| #![trigger a@[k], b@[k], c@[k]] 0 <= k < i ==> forall|j: int| #![auto] 0 <= j < c@[k].len() ==> c@[k][j] == a@[k][j] + b@[k][j],
        decreases a.len() - i
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j = 0;
        while j < a[i].len()
            invariant
                i < a.len(),
                j <= a@[i as int].len(),
                row.len() == j,
                forall|k: int| #![auto] 0 <= k < j ==> row@[k] == a@[i as int][k] + b@[i as int][k],
            decreases a@[i as int].len() - j
        {
            let sum = a[i][j] + b[i][j];
            row.push(sum);
            j += 1;
        }
        c.push(row);
        i += 1;
    }
    c
}
// </vc-code>

}
fn main() {}