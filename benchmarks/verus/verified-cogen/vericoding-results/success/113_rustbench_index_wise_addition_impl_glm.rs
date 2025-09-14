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
    /* code modified by LLM (iteration 3): added triggers to quantifier in loop invariant */
    let mut c: Vec<Vec<i32>> = Vec::new();
    for i in 0..a.len()
        invariant
            c.len() == i,
            forall|k: int| 0 <= k < i ==> c[k].len() == a[k].len(),
            forall|k: int| #![trigger c[k]] 0 <= k < i ==> 
                forall|j: int| #![trigger c[k][j]] 0 <= j < c[k].len() ==> c[k][j] == a[k][j] + b[k][j],
    {
        let inner_a = &a[i];
        let inner_b = &b[i];
        let mut inner_c = Vec::new();
        for j in 0..inner_a.len()
            invariant
                inner_c.len() == j,
                forall|k: int| 0 <= k < j ==> inner_c[k] == inner_a[k] + inner_b[k],
        {
            inner_c.push(inner_a[j] + inner_b[j]);
        }
        c.push(inner_c);
    }
    c
}
// </vc-code>

}
fn main() {}