// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause to loop */
#[verifier::loop_isolation(false)]
fn add_rows(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    requires
        a.len() == b.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> a[i] + b[i] <= i32::MAX,
        forall|i: int| #![auto] 0 <= i < a.len() ==> a[i] + b[i] >= i32::MIN,
    ensures
        c.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < c.len() ==> c[i] == a[i] + b[i],
{
    let mut c = Vec::new();
    let mut j: usize = 0;
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            a.len() == b.len(),
            c.len() == j,
            forall|k: int| 0 <= k < j ==> c[k] == a[k] + b[k],
            forall|k: int| #![auto] 0 <= k < a.len() ==> a[k] + b[k] <= i32::MAX,
            forall|k: int| #![auto] 0 <= k < a.len() ==> a[k] + b[k] >= i32::MIN,
        decreases a.len() - j
    {
        let val = a[j] + b[j];
        c.push(val);
        j = j + 1;
    }
    c
}
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
    /* code modified by LLM (iteration 2): added decreases clause to loop */
    let mut c: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            forall|k: int| #![auto] 0 <= k < a.len() ==> a[k].len() == b[k].len(),
            forall|k: int| #![trigger a[k], b[k]] 0 <= k < a.len() ==> forall|j: int| 0 <= j < a[k].len() ==> a[k][j] + b[k][j] <= i32::MAX,
            forall|k: int| #![trigger a[k], b[k]] 0 <= k < a.len() ==> forall|j: int| 0 <= j < a[k].len() ==> a[k][j] + b[k][j] >= i32::MIN,
            c.len() == i,
            forall|k: int| #![auto] 0 <= k < i ==> c[k].len() == a[k].len(),
            forall|k: int| #![trigger a[k], b[k], c[k]] 0 <= k < i ==> forall|j: int| #![auto] 0 <= j < c[k].len() ==> c[k][j] == a[k][j] + b[k][j],
        decreases a.len() - i
    {
        let new_row = add_rows(&a[i], &b[i]);
        c.push(new_row);
        i = i + 1;
    }
    c
}
// </vc-code>

}
fn main() {}