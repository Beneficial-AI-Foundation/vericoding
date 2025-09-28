// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The body of a `spec` function cannot contain arbitrary Rust code, it can only contain ghost code. */
pub open spec fn calculate_freq_val(i: int, d: int, n: int) -> int
    requires
        d > 0,
        n > 0,
    ensures
        calculate_freq_val(i, d, n) == i / (d * n)
{
    i / (d * n)
}
// </vc-helpers>

// <vc-spec>
fn numpy_rfftfreq(n: usize, d: i8) -> (result: Vec<i8>)
    requires 
        n > 0,
        d > 0,
    ensures
        result.len() == n / 2 + 1,
        result@[0] == 0,
        forall|i: int| 0 <= i < result.len() ==> result@[i] == i / ((d as int) * (n as int)),
        result@[(n / 2) as int] == (n / 2) as int / ((d as int) * (n as int)),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result@[i] <= result@[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The Verus types `nat` and `int` can only be used in ghost code. Moved casting to `int` within the `while` loop into a `proof` block for the calculation of `val_int` and then casting `val_int` to i8 for `val`. */
{
    let mut result: Vec<i8> = Vec::with_capacity(n / 2 + 1);

    result.push(0);

    let mut i: usize = 1;
    while i <= n / 2
        invariant
            result.len() == i,
            (forall|k: int| 0 <= k < result.len() ==> result@[k] ==
                ({
                    let n_int: int = n as int;
                    let d_int: int = d as int;
                    calculate_freq_val(k, d_int, n_int)
                }) as i8),
            (forall|k: int| 0 <= k < result.len() - 1 ==> result@[k] <= result@[k+1]),
            i <= n / 2 + 1,
    {
        proof {
            let n_int: int = n as int;
            let d_int: int = d as int;
            let val_int: int = calculate_freq_val(i as int, d_int, n_int);
            assert (val_int == (i as int / (d_int * n_int)));
        }
        let val: i8 = (((i as int) / ((d as int) * (n as int))) as i8);
        result.push(val);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}