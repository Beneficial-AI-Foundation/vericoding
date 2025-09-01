use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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

    let mut i: nat = 0;
    while i < a.len()
        invariant i <= a.len();
        invariant c.len() == i;
        invariant forall|k: nat| #![trigger a[k], b[k], c[k]]
            k < i ==> c[k].len() == a[k].len();
        invariant forall|k: nat| #![trigger a[k], b[k], c[k]]
            k < i ==> forall|j: nat| j < c[k].len() ==> c[k][j] == a[k][j] + b[k][j];
        decreases a.len() - i;
    {
        // ensure we can index a[i]
        assert(i < a.len());

        let mut row: Vec<i32> = Vec::new();
        let mut j: nat = 0;
        while j < a[i].len()
            invariant j <= a[i].len();
            invariant row.len() == j;
            invariant forall|k: nat| k < j ==> row[k] == a[i][k] + b[i][k];
            decreases a[i].len() - j;
        {
            row.push(a[i][j] + b[i][j]);
            j = j + 1;
        }

        c.push(row);

        i = i + 1;
    }

    c
    // impl-end
}
// </vc-code>

fn main() {}
}