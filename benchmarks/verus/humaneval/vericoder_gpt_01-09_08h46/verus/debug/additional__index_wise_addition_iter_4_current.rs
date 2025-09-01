use vstd::prelude::*;

verus! {

// <vc-helpers>
// no changes
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
    let n = a.len();
    let mut c_res: Vec<Vec<i32>> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            c_res.len() == i,
            a.len() == n,
            b.len() == n,
            forall|k: int| #![trigger a[k], b[k]] 0 <= k < n ==> a[k].len() == b[k].len(),
            forall|k: int| #![trigger c_res[k], a[k]] 0 <= k < i ==> c_res[k].len() == a[k].len(),
            forall|k: int| #![trigger c_res[k]]
                0 <= k < i ==>
                    forall|j: int| #![trigger c_res[k][j]] 0 <= j < a[k].len()
                        ==> c_res[k][j] == a[k][j] + b[k][j],
            forall|k: int|
                0 <= k < n ==>
                    forall|j: int| #![trigger a[k][j], b[k][j]] 0 <= j < a[k].len()
                        ==> a[k][j] + b[k][j] <= i32::MAX,
            forall|k: int|
                0 <= k < n ==>
                    forall|j: int| #![trigger a[k][j], b[k][j]] 0 <= j < a[k].len()
                        ==> a[k][j] + b[k][j] >= i32::MIN
        decreases (n - i) as int
    {
        let ai = &a[i];
        let bi = &b[i];
        assert(ai.len() == bi.len());

        let m = ai.len();
        let mut row: Vec<i32> = Vec::new();

        let mut j: usize = 0;
        while j < m
            invariant
                j <= m,
                row.len() == j,
                m == ai.len(),
                bi.len() == m,
                forall|t: int| #![trigger row[t]] 0 <= t < j ==> row[t] == ai[t] + bi[t],
                forall|t: int| #![trigger ai[t], bi[t]] 0 <= t < m ==> ai[t] + bi[t] <= i32::MAX,
                forall|t: int| #![trigger ai[t], bi[t]] 0 <= t < m ==> ai[t] + bi[t] >= i32::MIN
            decreases (m - j) as int
        {
            let s = ai[j] + bi[j];
            row.push(s);
            assert(row[j as int] == s);
            j += 1;
        }

        assert(row.len() == m);
        c_res.push(row);
        i += 1;
    }

    c_res
}
// </vc-code>

fn main() {}
}