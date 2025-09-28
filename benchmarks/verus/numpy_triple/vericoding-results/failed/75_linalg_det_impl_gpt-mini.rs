// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute matrix minor by removing row rm and column cm */
fn minor(a: Vec<Vec<i8>>, rm: nat, cm: nat) -> Vec<Vec<i8>>
    requires
        a.len() > 0,
        rm < a.len(),
        cm < a.len(),
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() == a@.len(),
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == result@.len(),
{
    let n = a.len();
    let mut res: Vec<Vec<i8>> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant
            i <= n,
            res.len() == if i <= rm { i } else { i - 1 },
        decreases n - i
    {
        if i != rm {
            let mut row: Vec<i8> = Vec::new();
            let mut j: nat = 0;
            while j < n
                invariant
                    j <= n,
                    row.len() == if j <= cm { j } else { j - 1 },
                decreases n - j
            {
                if j != cm {
                    row.push(a[i][j]);
                }
                j += 1;
            }
            // after inner loop, row has length n-1
            assert(row.len() == n - 1);
            res.push(row);
        }
        i += 1;
    }
    // after outer loop, res has length n-1
    assert(res.len() == n - 1);
    // prove each row has length equal to res.len()
    let mut k: nat = 0;
    while k < res.len()
        invariant
            k <= res.len(),
            forall|ii: int| 0 <= ii < k ==> res@[ii].len() == res.len(),
        decreases res.len() - k
    {
        assert(res[k].len() == n - 1);
        k += 1;
    }
    res
}

// </vc-helpers>

// <vc-spec>
fn det(a: Vec<Vec<i8>>) -> (result: i8)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() == a@.len(),
    ensures
        /* For 1x1 matrices, the determinant is the single element */
        a@.len() == 1 ==> result as int == a@[0][0],
        /* For 2x2 matrices, the determinant is ad - bc */
        a@.len() == 2 ==> result as int == a@[0][0] * a@[1][1] - a@[0][1] * a@[1][0],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): determinant via expansion by first row using minor helper */
    let n = a.len();
    if n == 1 {
        a[0][0]
    } else if n == 2 {
        let v00 = a[0][0];
        let v01 = a[0][1];
        let v10 = a[1][0];
        let v11 = a[1][1];
        v00 * v11 - v01 * v10
    } else {
        let mut sum: i8 = 0;
        let mut j: nat = 0;
        while j < n
            invariant
                j <= n,
            decreases n - j
        {
            let sign: i8 = if j % 2 == 0 { 1 } else { -1 };
            let m = minor(a.clone(), 0, j);
            proof {
                assert(m.len() == n - 1);
                assert(m.len() > 0);
                assert(forall|ii: int| 0 <= ii < m@.len() ==> m@[ii].len() == m@.len());
            }
            let sub = det(m);
            let term = a[0][j] * sub;
            sum = sum + sign * term;
            j += 1;
        }
        sum
    }
}

// </vc-code>


}
fn main() {}