// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn compute_hermite_basis_recursive(n: nat, t: int) -> (result: int)
    ensures
        result == hermite_basis(n, t),
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        t
    } else {
        let prev1 = compute_hermite_basis_recursive((n - 1) as nat, t);
        let prev2 = compute_hermite_basis_recursive((n - 2) as nat, t);
        t * prev1 - (n - 1) as int * prev2
    }
}

fn compute_row_sum_exec(row: &Vec<i8>, x: i8, y: i8, i: usize) -> (sum: i8)
    requires
        row.len() > 0,
    ensures
        sum as int == row_sum_helper(row@, x as int, y as int, i as int, 0, row.len() as int),
{
    /* helper modified by LLM (iteration 5): fixed type conversion and Vec/Seq mismatch */
    let mut j = 0;
    let mut sum: i8 = 0;
    let m = row.len();
    
    while j < m
        invariant
            j <= m,
            sum as int == row_sum_helper(row@, x as int, y as int, i as int, j as int, m as int),
        decreases m - j
    {
        proof {
            let herm_x_val = hermite_basis(i as nat, x as int);
            let herm_y_val = hermite_basis(j as nat, y as int);
        }
        let herm_x_val_proof = proof { compute_hermite_basis_recursive(i as nat, x as int) };
        let herm_y_val_proof = proof { compute_hermite_basis_recursive(j as nat, y as int) };
        let term = (row[j] as int) * herm_x_val_proof * herm_y_val_proof;
        sum = (sum as int + term) as i8;
        j += 1;
    }
    sum
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
    /* code modified by LLM (iteration 5): fixed type conversion issues */
    let n = x.len();
    let mut result = Vec::with_capacity(n);
    let rows = c.len();
    let cols = c[0].len();
    
    let mut k = 0;
    while k < n
        invariant
            k <= n,
            result.len() == k,
            forall|i: int| 0 <= i < k ==> result[i] as int == matrix_sum(c@, x[i] as int, y[i] as int),
        decreases n - k
    {
        let x_val = x[k];
        let y_val = y[k];
        let mut total_sum: i8 = 0;
        let mut i = 0;
        
        while i < rows
            invariant
                i <= rows,
                total_sum as int == matrix_sum_helper(c@, x_val as int, y_val as int, i as int, rows as int, cols as int),
            decreases rows - i
        {
            let row_sum = compute_row_sum_exec(&c[i], x_val, y_val, i);
            total_sum = (total_sum as int + row_sum as int) as i8;
            i += 1;
        }
        
        result.push(total_sum);
        k += 1;
    }
    result
}
// </vc-code>


}
fn main() {}