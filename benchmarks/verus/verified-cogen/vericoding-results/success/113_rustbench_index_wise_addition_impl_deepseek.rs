// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fix fn type conversion to spec functions */
spec fn is_valid_index(i: int, len: int) -> bool { 0 <= i < len }
proof fn preserves_lengths(a: &Vec<Vec<i32>>, b: &Vec<Vec<i32>>, i: int) 
    requires 
        a.len() == b.len(),
        forall|k: int| #![auto] 0 <= k < a.len() ==> a[k].len() == b[k].len(),
        0 <= i < a.len()
    ensures 
        a[i].len() == b[i].len()
{
}
proof fn addition_within_bounds(a: &Vec<Vec<i32>>, b: &Vec<Vec<i32>>, i: int, j: int) 
    requires 
        forall|k: int| #![trigger a[k], b[k]] 0 <= k < a.len() ==> forall|l: int| 0 <= l < a[k].len() ==> a[k][l] + b[k][l] <= i32::MAX,
        forall|k: int| #![trigger a[k], b[k]] 0 <= k < a.len() ==> forall|l: int| 0 <= l < a[k].len() ==> a[k][l] + b[k][l] >= i32::MIN,
        0 <= i < a.len(),
        0 <= j < a[i].len()
    ensures 
        a[i][j] + b[i][j] <= i32::MAX && a[i][j] + b[i][j] >= i32::MIN
{
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
/* code modified by LLM (iteration 3): fix type conversion in array indexing */
{
    let mut c: Vec<Vec<i32>> = Vec::new();
    let mut outer_i: usize = 0;
    
    while outer_i < a.len()
        invariant
            0 <= outer_i <= a.len(),
            c.len() == outer_i,
            forall|k: int| 0 <= k < outer_i ==> c[k].len() == a[k].len(),
            forall|k: int| #![trigger a[k], b[k], c[k]] 0 <= k < outer_i ==> forall|l: int| 0 <= l < c[k].len() ==> c[k][l] == a[k][l] + b[k][l]
        decreases a.len() - outer_i
    {
        let inner_len = a[outer_i].len();
        let mut inner_vec: Vec<i32> = Vec::new();
        let mut inner_j: usize = 0;
        
        while inner_j < inner_len
            invariant
                0 <= inner_j <= inner_len,
                inner_vec.len() == inner_j,
                forall|l: int| 0 <= l < inner_j ==> inner_vec[l] == a[outer_i as int][l] + b[outer_i as int][l]
            decreases inner_len - inner_j
        {
            proof { preserves_lengths(a, b, outer_i as int); }
            proof { addition_within_bounds(a, b, outer_i as int, inner_j as int); }
            let sum = a[outer_i][inner_j] + b[outer_i][inner_j];
            inner_vec.push(sum);
            inner_j += 1;
        }
        
        c.push(inner_vec);
        outer_i += 1;
    }
    
    c
}
// </vc-code>

}
fn main() {}