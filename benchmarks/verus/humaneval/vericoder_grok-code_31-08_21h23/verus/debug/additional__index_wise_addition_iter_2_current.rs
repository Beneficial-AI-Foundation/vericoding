use vstd::prelude::*;

verus! {

// <vc-helpers>
//
// </vc-helpers>
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
    let ghost a_seq: Seq<Seq<i32>> = a@.map(|x| x@);
    let ghost b_seq: Seq<Seq<i32>> = b@.map(|x| x@);

    let mut i: usize = 0;
    while i < a_len
        invariant
            0 <= i <= a_len,
            c@.len() == i,
            forall |k: int| #![auto] 0 <= k < i ==> c@[k].len() as int == a_seq[k].len() as int,
            forall |k: int| #![trigger a_seq[k], c@[k]]
                0 <= k < i
                    ==> forall |l: int| #![auto] 0 <= l < a_seq[k].len() ==> c@[k][l] == a_seq[k][l] + b_seq[k][l],
    {
        let a_row = &a[i];
        let b_row = &b[i];
        let a_row_len = a_row.len();
        let mut row: Vec<i32> = Vec::new();

        let mut j: usize = 0;
        while j < a_row_len
            invariant
                0 <= j <= a_row_len,
                row@.len() == j,
                forall |m: int| #![auto] 0 <= m < j ==> row@[m] == a_seq[i][m] + b_seq[i][m],
        {
            let sum = a_row[j] + b_row[j];
            row.push(sum);
            j += 1;
        }

        c.push(row);
        i += 1;
    }

    c
}
// </vc-code>

fn main() {}
}