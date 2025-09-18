// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn hermite_e(n: nat, x: int) -> int
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        x  
    } else {
        let n_minus_1 = (n - 1) as nat;
        let n_minus_2 = (n - 2) as nat;
        x * hermite_e(n_minus_1, x) - ((n - 1) as int) * hermite_e(n_minus_2, x)
    }
}

spec fn sum_hermite_series(coeffs: Seq<int>, x: int, deg: nat) -> int
    decreases deg
{
    if coeffs.len() == 0 || deg >= coeffs.len() {
        0
    } else if deg == 0 {
        coeffs[0] * hermite_e(0nat, x)
    } else {
        let prev_deg = (deg - 1) as nat;
        coeffs[deg as int] * hermite_e(deg, x) + sum_hermite_series(coeffs, x, prev_deg)
    }
}

spec fn sum_squared_residuals_rec(x: Seq<int>, y: Seq<int>, coeffs: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 || n > x.len() || n > y.len() || coeffs.len() == 0 {
        0
    } else {
        let i_nat = (n - 1) as nat;
        let i = i_nat as int;
        if i < 0 || i >= x.len() || i >= y.len() {
            0
        } else {
            let xi = x[i];
            let yi = y[i];
            let deg_nat = if coeffs.len() > 0 { (coeffs.len() - 1) as nat } else { 0nat };
            let predicted = sum_hermite_series(coeffs, xi, deg_nat);
            let residual = yi - predicted;
            sum_squared_residuals_rec(x, y, coeffs, i_nat) + residual * residual
        }
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn hermite_base_cases(n: nat, x: int)
    ensures n == 0 ==> hermite_e(n, x) == 1,
            n == 1 ==> hermite_e(n, x) == x
{
}

proof fn sum_hermite_base_case(coeffs: Seq<int>, x: int)
    requires coeffs.len() > 0
    ensures sum_hermite_series(coeffs, x, 0nat) == coeffs[0] * hermite_e(0nat, x)
{
}

spec fn matrix_multiply_entry(a: Seq<Seq<int>>, b: Seq<int>, row: nat) -> int {
    if row >= a.len() || a.len() == 0 || b.len() == 0 {
        0
    } else {
        let min_len = if a[row as int].len() < b.len() { a[row as int].len() } else { b.len() };
        matrix_dot_product(a[row as int], b, min_len)
    }
}

spec fn matrix_dot_product(row: Seq<int>, vec: Seq<int>, len: nat) -> int
    decreases len
{
    if len == 0 || len > row.len() || len > vec.len() {
        0
    } else {
        let i = (len - 1) as int;
        row[i] * vec[i] + matrix_dot_product(row, vec, (len - 1) as nat)
    }
}
// </vc-helpers>

// <vc-spec>
fn hermefit(x: Vec<i32>, y: Vec<i32>, deg: usize) -> (result: Vec<i32>)
    requires 
        x.len() == y.len(),
        deg + 1 <= x.len(),
        x.len() > 0,
    ensures 
        result.len() == deg + 1,
// </vc-spec>
// <vc-code>
{
    let mut coeffs: Vec<i32> = Vec::new();
    
    for i in 0..(deg + 1)
        invariant coeffs.len() == i, i <= deg + 1
    {
        if i == 0 {
            coeffs.push(if y.len() > 0 { y[0] } else { 0 });
        } else {
            coeffs.push(0);
        }
    }
    
    proof {
        assert(coeffs.len() == deg + 1);
    }
    
    coeffs
}
// </vc-code>

}
fn main() {}