use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_vec_len_eq<T>(v1: &Vec<Vec<T>>, v2: &Vec<Vec<T>>)
    requires
        v1.len() == v2.len(),
        forall|i: int| 0 <= i < v1.len() ==> (#[trigger] v1[i]).len() == (#[trigger] v2[i]).len(),
    ensures
        forall|i: int| 0 <= i < v1.len() ==> v1@.index(i).len() == v2@.index(i).len(),
{
    assert forall|i: int| 0 <= i < v1.len() implies v1@.index(i).len() == v2@.index(i).len() by {
        assert(v1@.index(i).len() == v1[i].len());
        assert(v2@.index(i).len() == v2[i].len());
    }
}

proof fn lemma_vec_addition_bounds(a: &Vec<Vec<i32>>, b: &Vec<Vec<i32>>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a[i].len(),
        forall|k: int| 0 <= k < a.len() ==> a[k].len() == b[k].len(),
        forall|k: int| 
            0 <= k < a.len()
                ==> forall|l: int| 0 <= l < a[k].len() ==> a[k][l] + b[k][l] <= i32::MAX,
        forall|k: int| 
            0 <= k < a.len()
                ==> forall|l: int| 0 <= l < a[k].len() ==> a[k][l] + b[k][l] >= i32::MIN,
    ensures
        a[i][j] + b[i][j] <= i32::MAX,
        a[i][j] + b[i][j] >= i32::MIN,
{
}

proof fn lemma_vec_addition_bounds_usize(a: &Vec<Vec<i32>>, b: &Vec<Vec<i32>>, i: usize, j: usize)
    requires
        i < a.len(),
        j < a[i].len(),
        forall|k: int| 0 <= k < a.len() ==> a[k].len() == b[k].len(),
        forall|k: int| 
            0 <= k < a.len()
                ==> forall|l: int| 0 <= l < a[k].len() ==> a[k][l] + b[k][l] <= i32::MAX,
        forall|k: int| 
            0 <= k < a.len()
                ==> forall|l: int| 0 <= l < a[k].len() ==> a[k][l] + b[k][l] >= i32::MIN,
    ensures
        a[i][j] + b[i][j] <= i32::MAX,
        a[i][j] + b[i][j] >= i32::MIN,
{
    proof {
        lemma_vec_addition_bounds(a, b, i as int, j as int);
    }
}
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
    let mut outer_idx: usize = 0;
    
    while outer_idx < a.len()
        invariant
            outer_idx <= a.len(),
            c.len() == outer_idx,
            forall|i: int| 0 <= i < outer_idx ==> c[i].len() == a[i].len(),
            forall|i: int| 0 <= i < outer_idx ==> 
                forall|j: int| 0 <= j < a[i].len() ==> c[i][j] == a[i][j] + b[i][j],
    {
        let mut inner_vec: Vec<i32> = Vec::new();
        let mut inner_idx: usize = 0;
        let a_outer = &a[outer_idx];
        let b_outer = &b[outer_idx];
        
        while inner_idx < a_outer.len()
            invariant
                inner_idx <= a_outer.len(),
                inner_vec.len() == inner_idx,
                forall|j: int| 0 <= j < inner_idx ==> 
                    inner_vec[j] == a_outer[j] + b_outer[j],
        {
            proof {
                lemma_vec_addition_bounds_usize(a, b, outer_idx, inner_idx);
            }
            let sum = a_outer[inner_idx] + b_outer[inner_idx];
            inner_vec.push(sum);
            inner_idx += 1;
        }
        
        c.push(inner_vec);
        outer_idx += 1;
    }
    
    lemma_vec_len_eq(a, b);
    c
}
// </vc-code>

fn main() {}
}