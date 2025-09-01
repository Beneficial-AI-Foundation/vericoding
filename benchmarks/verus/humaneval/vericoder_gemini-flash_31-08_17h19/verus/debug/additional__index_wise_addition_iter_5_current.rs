use vstd::prelude::*;

verus! {

// <vc-helpers>
fn get_total_len(v: &Vec<Vec<i32>>) -> (total_len: usize)
    ensures total_len == v.len()
{
    v.len()
}

fn get_inner_len(v: &Vec<i32>) -> (total_len: usize)
    ensures total_len == v.len()
{
    v.len()
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
    let a_len = a.len();
    let b_len_val = b.len();

    // Loop invariant for the outer loop
    assert(a_len == b_len_val);

    #[verifier::loop_invariant_param(c, a, b)]
    #[verifier::loop_invariant(
        c.len() == i_usize,
        i_usize <= a_len,
        forall|k: int| 0 <= k < i_usize as int ==> #[trigger] c[k as usize].len() == a[k as usize].len(),
        forall|k: int| 0 <= k < i_usize as int ==> forall|l: int| 0 <= l < c[k as usize].len() ==> #[trigger] c[k as usize][l as usize] == a[k as usize][l as usize] + b[k as usize][l as usize]
    )]
    for i_usize in 0..a_len {
        // let i = i_usize as int; // Changed to int for usage in forall
        let mut inner_c: Vec<i32> = Vec::new();
        let a_inner_len = a[i_usize].len();
        let b_inner_len_val = b[i_usize].len();

        assert(a_inner_len == b_inner_len_val);

        #[verifier::loop_invariant_param(inner_c, a, b)] // Pass a and b to the inner loop
        #[verifier::loop_invariant(
            inner_c.len() == j_usize,
            j_usize <= a_inner_len,
            forall|k: int| 0 <= k < j_usize as int ==> #[trigger] inner_c[k as usize] == a[i_usize][k as usize] + b[i_usize][k as usize]
        )]
        for j_usize in 0..a_inner_len {
            // let j = j_usize as int; // Changed to int for usage in forall
            inner_c.push(a[i_usize][j_usize] + b[i_usize][j_usize]);
        }
        c.push(inner_c);
    }
    c
}
// </vc-code>

fn main() {}
}