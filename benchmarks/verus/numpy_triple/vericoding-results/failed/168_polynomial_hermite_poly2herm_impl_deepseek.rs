// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed hermite_basis functions to properly declare result variables */
fn hermite_basis_0() -> f64 
    ensures
        result == 1.0,
{
    let result = 1.0;
    result
}

fn hermite_basis_1(x: f64) -> f64 
    ensures
        result == 2.0 * x,
{
    let result = 2.0 * x;
    result
}

fn hermite_basis_2(x: f64) -> f64 
    ensures
        result == 4.0 * x * x - 2.0,
{
    let result = 4.0 * x * x - 2.0;
    result
}

fn hermite_basis_3(x: f64) -> f64 
    ensures
        result == 8.0 * x * x * x - 12.0 * x,
{
    let result = 8.0 * x * x * x - 12.0 * x;
    result
}

spec fn hermite_basis(n: int, x: f64) -> f64 {
    if n == 0 {
        1.0
    } else if n == 1 {
        2.0 * x
    } else if n == 2 {
        4.0 * x * x - 2.0
    } else if n == 3 {
        8.0 * x * x * x - 12.0 * x
    } else {
        0.0
    }
}

spec fn sum_hermite(coefficients: Seq<f64>, n: int, x: f64) -> f64 {
    if n <= 0 {
        0.0
    } else {
        sum_hermite(coefficients, n - 1, x) + coefficients[n - 1] * hermite_basis(n - 1, x)
    }
}

fn hermite_eval(coefficients: Seq<f64>, x: f64) -> (result: f64)
    requires
        coefficients.len() >= 0,
    ensures
        (forall|i: int| 0 <= i < coefficients.len() ==> coefficients[i] == 0.0) ==> result == 0.0,
{
    if coefficients.len() == 0 {
        let result = 0.0;
        result
    } else {
        let mut res = 0.0;
        let mut i = 0;
        while i < coefficients.len()
            invariant
                0 <= i <= coefficients.len(),
                res == sum_hermite(coefficients, i, x),
            decreases coefficients.len() - i,
        {
            let basis = hermite_basis(i, x);
            res = res + coefficients[i] * basis;
            i += 1;
        }
        let result = res;
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn poly2herm(pol: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == pol.len(),

        (forall|i: int| 0 <= i < pol@.len() ==> pol@[i] == 0.0) ==> 
            (forall|i: int| 0 <= i < result@.len() ==> result@[i] == 0.0),

        pol.len() > 0 ==> 
            (forall|i: int| 1 <= i < pol@.len() ==> pol@[i] == 0.0) ==>
                result@[0] == pol@[0],

        (pol.len() == 4 && pol@[0] == 0.0 && pol@[1] == 1.0 && 
         pol@[2] == 2.0 && pol@[3] == 3.0) ==>
            (result@[0] == 1.0 && result@[1] == 2.75 && 
             result@[2] == 0.5 && result@[3] == 0.375)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed result variable declaration and return values */
    let len = pol.len();
    if len == 0 {
        pol
    } else {
        let mut result = Vec::<f64>::new();
        let mut i = 0;
        while i < len
            invariant
                0 <= i <= len,
                result@.len() == i,
                (forall|j: int| 0 <= j < pol@.len() ==> pol@[j] == 0.0) ==> 
                    (forall|j: int| 0 <= j < result@.len() ==> result@[j] == 0.0),
                pol@.len() > 0 && (forall|j: int| 1 <= j < pol@.len() ==> pol@[j] == 0.0) ==>
                    result@.len() > 0 && result@[0] == pol@[0],
            decreases len - i,
        {
            let coef_seq = pol@.subrange(0, i + 1);
            let val = hermite_eval(coef_seq, 0.0);
            result.push(val);
            i += 1;
        }
        result
    }
}
// </vc-code>

}
fn main() {}