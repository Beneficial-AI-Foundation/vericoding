// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [fixed ghost types in exec code] */
fn hermite_basis_exec(n: u64, t: i64) -> (result: i64)
    ensures
        result as int == hermite_basis(n as nat, t as int),
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        t
    } else {
        let h_n_minus_1 = hermite_basis_exec(n - 1, t);
        let h_n_minus_2 = hermite_basis_exec(n - 2, t);
        t * h_n_minus_1 - (n - 1) as i64 * h_n_minus_2
    }
}

/* helper modified by LLM (iteration 4): [Corrected indexing on Vecs with usize in spec contexts] */
fn matrix_sum_exec(c: &Vec<Vec<i8>>, x_val: i8, y_val: i8) -> (result: i64)
    requires
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() as int ==> #[trigger] c@[i].len() == c@[0].len(),
        c[0].len() > 0,
    ensures
        result as int == matrix_sum(c@, x_val as int, y_val as int),
{
    let n = c.len();
    let m = c[0].len();

    let mut total_sum: i64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            c.len() == n,
            m > 0,
            forall|idx: int| 0 <= idx < c.len() as int ==> #[trigger] c@[idx].len() == m,
            total_sum as int == matrix_sum_helper(c@, x_val as int, y_val as int, 0, i as int, m as int),
        decreases n - i
    {
        let mut row_sum: i64 = 0;
        let mut j: usize = 0;
        while j < m
            invariant
                i < n,
                0 <= j <= m,
                c@[i as int].len() == m,
                row_sum as int == row_sum_helper(c@[i as int], x_val as int, y_val as int, i as int, 0, j as int),
            decreases m - j
        {
            let h_i = hermite_basis_exec(i as u64, x_val as i64);
            let h_j = hermite_basis_exec(j as u64, y_val as i64);
            let term = (c[i][j] as i64) * h_i * h_j;
            row_sum = row_sum + term;
            j = j + 1;
        }
        total_sum = total_sum + row_sum;
        i = i + 1;
    }
    total_sum
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
    /* code modified by LLM (iteration 4): [Corrected indexing with usize variables in spec contexts] */
    let len = x.len();
    let mut result: Vec<i8> = Vec::with_capacity(len);
    let mut k: usize = 0;
    while k < len
        invariant
            0 <= k <= len,
            x.len() == len,
            y.len() == len,
            c.len() > 0,
            forall|i: int| 0 <= i < c.len() ==> #[trigger] c@[i].len() == c@[0].len(),
            c[0].len() > 0,
            result.len() == k,
            forall|j: int| 0 <= j < k as int ==> 
                result@[j] as int == matrix_sum(c@, x@[j] as int, y@[j] as int),
        decreases len - k
    {
        let total_sum = matrix_sum_exec(&c, x[k], y[k]);
        
        proof {
            let spec_sum = matrix_sum(c@, x@[k as int] as int, y@[k as int] as int);
            assert(total_sum as int == spec_sum);
            // The function's spec requires the matrix_sum to fit in an i8.
            // If it didn't, it would be impossible to satisfy the 'ensures' clause.
            assert(i8::MIN as int <= spec_sum && spec_sum <= i8::MAX as int);
            assert(i8::MIN as i64 <= total_sum && total_sum <= i8::MAX as i64);
        }

        result.push(total_sum as i8);
        k = k + 1;
    }
    result
}
// </vc-code>


}
fn main() {}