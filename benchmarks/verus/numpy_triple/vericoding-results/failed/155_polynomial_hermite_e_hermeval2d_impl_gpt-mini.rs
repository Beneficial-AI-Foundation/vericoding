// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable Hermite basis with ensures relating to spec */
fn hermite_basis_exec(n: usize, t: i64) -> i64
    ensures
        hermite_basis(n as nat, t as int) == result as int,
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        t
    } else {
        let a = hermite_basis_exec(n - 1, t);
        let b = hermite_basis_exec(n - 2, t);
        t * a - ((n - 1) as i64) * b
    }
}
// </vc-helpers>

// <vc-spec>
spec fn hermite_basis(n: nat, t: int) -> int
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        t
    } else {
        t * hermite_basis((n - 1) as nat, t) - (n - 1) as int * hermite_basis((n - 2) as nat, t)
    }
}

spec fn matrix_sum(c: Seq<Vec<i8>>, x: int, y: int) -> int {
    let n = c.len() as int;
    if n == 0 {
        0
    } else {
        let m = c[0].len() as int;
        matrix_sum_helper(c, x, y, 0, n, m)
    }
}

spec fn matrix_sum_helper(c: Seq<Vec<i8>>, x: int, y: int, i: int, n: int, m: int) -> int
    decreases n - i
{
    if i >= n {
        0
    } else {
        row_sum_helper(c[i], x, y, i, 0, m) + matrix_sum_helper(c, x, y, i + 1, n, m)
    }
}

spec fn row_sum_helper(row: Vec<i8>, x: int, y: int, i: int, j: int, m: int) -> int
    decreases m - j
{
    if j >= m {
        0
    } else {
        (row[j] as int) * hermite_basis(i as nat, x) * hermite_basis(j as nat, y) + 
        row_sum_helper(row, x, y, i, j + 1, m)
    }
}

fn hermeval2d(x: Vec<i8>, y: Vec<i8>, c: Vec<Vec<i8>>) -> (result: Vec<i8>)
    requires
        x.len() == y.len(),
        x.len() > 0,
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> #[trigger] c[i].len() == c[0].len(),
        c[0].len() > 0,
    ensures
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> 
            result[k] as int == matrix_sum(c@, x[k] as int, y[k] as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute 2D Hermite evaluation using executable helper and maintain invariants */
    let n: usize = c.len();
    let m: usize = c[0].len();
    let len: usize = x.len();

    let mut result: Vec<i8> = Vec::new();
    result.reserve(len);

    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            result.len() == k,
        decreases (len as int) - (k as int)
    {
        let xk: i64 = x[k] as i64;
        let yk: i64 = y[k] as i64;

        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i as int && i as int <= n as int,
            decreases (n as int) - (i as int)
        {
            let row_ref = &c[i];

            let mut row_sum: i64 = 0;
            let mut j: usize = 0;
            while j < m
                invariant
                    0 <= j as int && j as int <= m as int,
                decreases (m as int) - (j as int)
            {
                let term: i64 = (row_ref[j] as i64) * hermite_basis_exec(i, xk) * hermite_basis_exec(j, yk);
                row_sum = row_sum + term;
                j = j + 1;
            }

            total = total + row_sum;
            i = i + 1;
        }

        result.push(total as i8);
        k = k + 1;
    }

    result
}
// </vc-code>


}
fn main() {}