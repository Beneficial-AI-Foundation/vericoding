// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn hermite_basis_exec(n: u32, t: i8) -> (result: i8)
    ensures result as int == hermite_basis(n as nat, t as int)
{
    if n == 0 {
        1
    } else if n == 1 {
        t
    } else {
        let prev1 = hermite_basis_exec(n - 1, t);
        let prev2 = hermite_basis_exec(n - 2, t);
        t * prev1 - ((n - 1) as i8) * prev2
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
    let mut result = Vec::new();
    let n = c.len();
    let m = c[0].len();
    
    for k in 0..x.len()
        invariant
            result.len() == k,
            forall|idx: int| 0 <= idx < k ==> result[idx] as int == matrix_sum(c@, x[idx] as int, y[idx] as int),
    {
        let mut sum: i8 = 0;
        
        for i in 0..n
            invariant
                sum as int == matrix_sum_helper(c@, x[k] as int, y[k] as int, 0, i as int, m as int),
        {
            let mut row_sum: i8 = 0;
            let h_i = hermite_basis_exec(i as u32, x[k]);
            
            for j in 0..m
                invariant
                    row_sum as int == row_sum_helper(c[i]@, x[k] as int, y[k] as int, i as int, 0, j as int),
            {
                let h_j = hermite_basis_exec(j as u32, y[k]);
                row_sum = row_sum + c[i][j] * h_i * h_j;
            }
            
            sum = sum + row_sum;
        }
        
        result.push(sum);
    }
    
    result
}
// </vc-code>


}
fn main() {}