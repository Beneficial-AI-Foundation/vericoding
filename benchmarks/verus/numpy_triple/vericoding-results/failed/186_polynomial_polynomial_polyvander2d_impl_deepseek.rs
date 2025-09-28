// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn pow_spec(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow_spec(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed invalid cast in grand_len_nat declaration */

spec fn x_powers(x: f64, deg: u8) -> Seq<f64>
    decreases deg as int
{
    if deg == 0 {
        Seq::new(1, |i: int| pow_spec(x, i as nat))
    } else {
        x_powers(x, deg - 1).push(pow_spec(x, deg as nat))
    }
}

spec fn y_powers(y: f64, deg: u8) -> Seq<f64>
    decreases deg as int
{
    if deg == 0 {
        Seq::new(1, |i: int| pow_spec(y, i as nat))
    } else {
        y_powers(y, deg - 1).push(pow_spec(y, deg as nat))
    }
}

proof fn outer_product(grand_len: int, x_vec: Seq<f64>, y_vec: Seq<f64>) -> Seq<Seq<f64>>
    requires
        x_vec.len() == grand_len,
        y_vec.len() == grand_len,
    ensures
        result.len() == grand_len,
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == grand_len,
{
    let mut result = Seq::<Seq<f64>>::empty();
    let mut i = 0;
    while i < grand_len
        invariant
            i >= 0,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == grand_len,
        decreases grand_len - i
    {
        let mut row = Seq::<f64>::empty();
        let mut j = 0;
        while j < grand_len
            invariant
                j >= 0,
                row.len() == j,
                forall|p: int| 0 <= p < row.len() ==> row[p] == x_vec[i] * y_vec[p],
            decreases grand_len - j
        {
            row = row.push(x_vec[i] * y_vec[j]);
            j += 1;
        }
        result = result.push(row);
        i += 1;
    }
    result
}

proof fn flatten_product(grand_len: int, x_deg: u8, y_deg: u8, x_val: f64, y_val: f64) -> (row: Vec<f64>)
    requires
        grand_len >= 0,
    ensures
        row.len() == grand_len,
{
    ghost {
        let x_deg_int = x_deg as int;
        let y_deg_int = y_deg as int;
    }
    let mut result = Vec::<f64>::with_capacity(grand_len as usize);
    let mut i = 0;
    while i <= x_deg as int
        invariant
            i >= 0,
            i <= x_deg as int + 1,
            result.len() as int == i * (y_deg as int + 1),
        decreases x_deg as int - i + 1
    {
        let mut j = 0;
        while j <= y_deg as int
            invariant
                j >= 0,
                j <= y_deg as int + 1,
                result.len() as int == i * (y_deg as int + 1) + j,
            decreases y_deg as int - j + 1
        {
            let x_pow = pow_spec(x_val, i as nat);
            let y_pow = pow_spec(y_val, j as nat);
            result.push(x_pow * y_pow);
            j += 1;
        }
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn polyvander2d(x: Vec<f64>, y: Vec<f64>, x_deg: u8, y_deg: u8) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == (x_deg as int + 1) * (y_deg as int + 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed unnecessary ghost block */
{
    let n = x.len();
    let mut result = Vec::<Vec<f64>>::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == (x_deg as int + 1) * (y_deg as int + 1),
        decreases n - i
    {
        let row = flatten_product((x_deg as int + 1) * (y_deg as int + 1), x_deg, y_deg, x[i], y[i]);
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}