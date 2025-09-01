use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    let mut i: int = 0;
    while i < a.len() {
        invariant 0 <= i && i <= a.len();
        invariant c.len() == i;
        invariant forall |k: int| 0 <= k < i
            ==> c[k].len() == a[k].len();
        invariant forall |k: int| 0 <= k < i
            ==> forall |l: int| 0 <= l < c[k].len() ==> c[k][l] == a[k][l] + b[k][l];

        let mut row: Vec<i32> = Vec::new();
        let mut j: int = 0;
        while j < a[i].len() {
            invariant 0 <= j && j <= a[i].len();
            invariant row.len() == j;
            invariant forall |l: int| 0 <= l < j ==> row[l] == a[i][l] + b[i][l];

            let sum: i32 = a[i][j] + b[i][j];
            row.push(sum);
            j += 1;
        }

        assert(row.len() == a[i].len());
        c.push(row);
        i += 1;
    }

    c
}
// </vc-code>

fn main() {}
}