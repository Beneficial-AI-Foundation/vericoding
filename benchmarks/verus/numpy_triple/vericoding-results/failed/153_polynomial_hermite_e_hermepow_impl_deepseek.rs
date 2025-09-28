// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed integer type conversions and improved poly_multiply implementation */

spec fn hermepow_iter_spec(pow: u8, maxpower: u8, c_len: nat) -> bool {
    pow <= maxpower && maxpower <= 16 && c_len > 0
}

proof fn lemma_hermepow_zero_properties(result: Vec<f64>, c: Seq<f64>)
    requires
        result@.len() == 1,
        result@[0] == 1.0,
        c.len() > 0,
    ensures
        result@.len() == 1 && result@[0] == 1.0 &&
            (forall|i: int| 1 <= i < result@.len() ==> result@[i] == 0.0)
{
}

proof fn lemma_hermepow_one_properties(result: Vec<f64>, c: Seq<f64>)
    requires
        result@.len() == c.len(),
        forall|i: int| 0 <= i < c.len() ==> result@[i] == c[i],
    ensures
        result@.len() == c.len() &&
            (forall|i: int| 0 <= i < c.len() ==> result@[i] == c[i])
{
}

proof fn lemma_hermepow_length_properties(result: Vec<f64>, c: Seq<f64>, pow: u8)
    requires
        result@.len() == 1 + (c.len() as int - 1) * pow as int,
        c.len() > 0,
        pow >= 1,
    ensures
        result@.len() == 1 + (c.len() - 1) * pow as int,
        result@.len() > 0
{
}

spec fn pow_is_zero(pow: u8) -> bool {
    pow == 0
}

spec fn pow_is_one(pow: u8) -> bool {
    pow == 1
}

spec fn pow_is_greater_than_one(pow: u8) -> bool {
    pow >= 1
}

fn validate_pow_constraints(pow: u8, maxpower: u8) -> (b: bool)
    ensures
        b <==> (pow <= maxpower && maxpower <= 16)
{
    pow <= maxpower && maxpower <= 16
}

fn poly_multiply(a: Vec<f64>, b: Vec<f64>) -> (result: Vec<f64>)
    requires
        a.len() > 0,
        b.len() > 0,
    ensures
        result@.len() == a@.len() + b@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == (
            let mut sum_val = 0.0;
            for j in max(0, i - (b@.len() as int - 1))..min(i + 1, a@.len() as int) {
                sum_val = sum_val + a@[j] * b@[i - j];
            };
            sum_val
        )
{
    let len = a.len() + b.len() - 1;
    let mut res = Vec::with_capacity(len);
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            res@.len() == i,
            forall|k: int| 0 <= k < i ==> res@[k] == (
                let mut sum_val = 0.0;
                for j in max(0, k - (b@.len() as int - 1))..min(k + 1, a@.len() as int) {
                    sum_val = sum_val + a@[j] * b@[k - j];
                };
                sum_val
            )
        decreases len - i
    {
        let mut sum_val: f64 = 0.0;
        let mut j = max(0, i as int - (b.len() as int - 1)) as usize;
        let end = min(i + 1, a.len());
        while j < end
            invariant
                j <= end,
                sum_val == (
                    let mut partial = 0.0;
                    for k in max(0, i as int - (b.len() as int - 1)) as usize..j {
                        partial = partial + a[k] as f64 * b[i - k] as f64;
                    };
                    partial
                )
            decreases end - j
        {
            sum_val += a[j] as f64 * b[i - j] as f64;
            j += 1;
        }
        res.push(sum_val);
        i += 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn hermepow(c: Vec<f64>, pow: u8, maxpower: u8) -> (result: Vec<f64>)
    requires 
        pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures

        pow == 0 ==> result.len() == 1 && result[0] == 1.0 && 
            (forall|i: int| 1 <= i < result.len() ==> result[i] == 0.0),
        pow == 1 ==> result.len() == c.len() &&
            (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),

        pow as int >= 1 ==> result.len() == 1 + (c.len() - 1) * pow as int,

        pow as int >= 1 && c.len() > 0 ==> result.len() > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation errors and improved implementation */
    if !validate_pow_constraints(pow, maxpower) {
        return Vec::new();
    }
    
    if pow == 0 {
        let mut result: Vec<f64> = Vec::new();
        result.push(1.0);
        proof { lemma_hermepow_zero_properties(result, c@); }
        result
    } else if pow == 1 {
        let mut result = Vec::with_capacity(c.len());
        let mut i: usize = 0;
        while i < c.len()
            invariant
                i <= c.len(),
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == c@[j]
            decreases c.len() - i
        {
            result.push(c[i]);
            i += 1;
        }
        proof { lemma_hermepow_one_properties(result, c@); }
        result
    } else {
        let mut result = c.clone();
        let mut current_pow: u8 = 1;
        while current_pow < pow
            invariant
                current_pow <= pow,
                result@.len() == 1 + (c@.len() as int - 1) * current_pow as int,
                result@.len() > 0
            decreases pow - current_pow
        {
            let temp = poly_multiply(result, c.clone());
            result = temp;
            current_pow += 1;
        }
        proof { lemma_hermepow_length_properties(result, c@, pow); }
        result
    }
}
// </vc-code>

}
fn main() {}