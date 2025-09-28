// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): executable versions matching specs for hermite basis and matrix sum */
fn hermite_basis_exec(n: nat, t: int) -> (res: int)
    ensures
        res == hermite_basis(n, t),
{
    if n == 0 {
        1
    } else if n == 1 {
        t
    } else {
        let mut i: int = 1;
        let mut hm2: int = 1; // H_0(t)
        let mut hm1: int = t; // H_1(t)
        while i < n as int
            invariant
                1 <= i <= n as int,
                hm1 == hermite_basis(i as nat, t),
                hm2 == hermite_basis((i - 1) as nat, t),
            decreases n as int - i
        {
            let hi = t * hm1 - i * hm2;
            proof {
                assert(i + 1 >= 2);
                assert(hermite_basis((i + 1) as nat, t) == t * hermite_basis(i as nat, t) - i * hermite_basis((i - 1) as nat, t));
            }
            i = i + 1;
            hm2 = hm1;
            hm1 = hi;
        }
        hm1
    }
}

/* helper modified by LLM (iteration 2): executable computation of matrix_sum equal to spec */
fn matrix_sum_value(c: &Vec<Vec<i8>>, x: int, y: int) -> (res: int)
    requires
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> #[trigger] c[i].len() == c[0].len(),
        c[0].len() > 0,
    ensures
        res == matrix_sum(c@, x, y),
{
    let n_usize = c.len();
    let m_usize = c[0].len();
    let n_int: int = n_usize as int;
    let m_int: int = m_usize as int;

    let mut total: int = 0;
    let mut i: usize = 0;
    while i < n_usize
        invariant
            0 <= i as int <= n_int,
            total == matrix_sum_helper(c@, x, y, 0, i as int, m_int),
            forall|k: int| 0 <= k < i as int ==> #[trigger] c[k as usize].len() == m_usize,
        decreases n_usize - i
    {
        let row = &c[i];
        let mut row_sum: int = 0;
        let mut j: usize = 0;
        while j < m_usize
            invariant
                0 <= j as int <= m_int,
                // Use a clone for spec row consumption; clone preserves contents
                row_sum == row_sum_helper(row.clone(), x, y, i as int, 0, j as int),
            decreases m_usize - j
        {
            let coeff: int = row[j] as int;
            let hb_i: int = hermite_basis_exec(i as nat, x);
            let hb_j: int = hermite_basis_exec(j as nat, y);
            row_sum = row_sum + coeff * hb_i * hb_j;
            j = j + 1;
        }
        // Close the row invariant to full row length
        proof { assert(row_sum == row_sum_helper(row.clone(), x, y, i as int, 0, m_int)); }
        total = total + row_sum;
        i = i + 1;
    }
    proof { assert(total == matrix_sum_helper(c@, x, y, 0, n_int, m_int)); }
    total
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
    /* code modified by LLM (iteration 2): compute matrix_sum for each (x[k], y[k]) and collect into result */
    let n = x.len();
    let mut result: Vec<i8> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            result.len() == k,
            k <= n,
        decreases n - k
    {
        let sx: int = x[k] as int;
        let sy: int = y[k] as int;
        let val: int = matrix_sum_value(&c, sx, sy);
        let v_i8: i8 = val as i8;
        result.push(v_i8);
        k = k + 1;
    }
    result
}
// </vc-code>


}
fn main() {}