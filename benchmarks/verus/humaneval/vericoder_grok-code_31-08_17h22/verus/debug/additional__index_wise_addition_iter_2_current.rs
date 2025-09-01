use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty as no additional helpers are needed for this implementation
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
    // impl-start
    let mut c: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            c.len() == i,
            forall|k: int| #![auto] 0 <= k < i ==> c@[k].len() == a@[k].len(),
            forall|k: int| #![trigger a@[k], b@[k], c@[k]]
                0 <= k < i ==> forall|l: int| #![auto] 0 <= l < c@[k].len() ==>
                    c@[k]@[l] == a@[k]@[l] + b@[k]@[l],
    {
        let mut inner_vec: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < a[i].len()
            invariant
                j <= a@[i as int].len(),
                inner_vec.len() == j,
                forall|m: int| #![auto] 0 <= m < j ==> inner_vec@[m] == a@[i as int]@[m] + b@[i as int]@[m],
        {
            inner_vec.push(a[i][j] + b[i][j]);
            j += 1;
        }
        proof {
            // Intermediate assertions for verification
            assert(forall|l: int| 0 <= l < inner_vec.len() ==> inner_vec@[l] == a@[i as int]@[l] + b@[i as int]@[l]);
        }
        c.push(inner_vec);
        i += 1;
    }
    c
    // impl-end
}
// </vc-code>

fn main() {}
}