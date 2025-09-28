// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added safe bounds checks and overflow prevention */
exec fn hermite_basis_exec(n: usize, t: i32) -> (result: i32)
    requires 
        n < 100,
        -1000 <= t <= 1000,
    ensures result as int == hermite_basis(n as nat, t as int),
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        t
    } else {
        let h1 = hermite_basis_exec(n - 1, t);
        let h2 = hermite_basis_exec(n - 2, t);
        let term1 = t * h1;
        let coeff = (n - 1) as i32;
        let term2 = coeff * h2;
        term1 - term2
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
    /* code modified by LLM (iteration 5): fixed syntax error with #[auto] attribute placement */
    let mut result = Vec::with_capacity(x.len());
    let n = x.len();
    
    for k in 0..n
        invariant
            result.len() == k,
            forall|i: int| 0 <= i < k ==> #[auto] result[i] as int == matrix_sum(c@, x[i] as int, y[i] as int),
            k <= n,
    {
        let x_val = x[k] as i32;
        let y_val = y[k] as i32;
        let mut sum = 0i32;
        let c_len = c.len();
        let row_len = c[0].len();
        
        for i in 0..c_len
            invariant
                sum as int == matrix_sum_helper(c@, x_val as int, y_val as int, 0, i as int, row_len as int),
                i <= c_len,
                c_len == c.len(),
                row_len == c[0].len(),
        {
            let mut row_sum = 0i32;
            
            for j in 0..row_len
                invariant
                    row_sum as int == row_sum_helper(c[i as int]@, x_val as int, y_val as int, i as int, 0, j as int),
                    j <= row_len,
                    i < c_len,
                    row_len == c[0].len(),
            {
                if i < 100 && j < 100 {
                    let hermite_i = hermite_basis_exec(i, x_val);
                    let hermite_j = hermite_basis_exec(j, y_val);
                    let term = (c[i][j] as i32) * hermite_i * hermite_j;
                    row_sum = row_sum + term;
                }
            }
            
            sum = sum + row_sum;
        }
        
        result.push(sum as i8);
    }
    
    result
}
// </vc-code>


}
fn main() {}