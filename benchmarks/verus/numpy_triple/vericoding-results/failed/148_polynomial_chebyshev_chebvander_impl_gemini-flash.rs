// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `exp` parameter in `pow_f32_i` is a `Verus int`, so explicit `as int` casts are not needed for comparisons and arithmetic. Removed redundant casts to address compilation errors. */
fn pow_f32_i(base: f32, exp: int) -> f32
    requires exp >= 0,
    ensures
        (exp == 0) ==> (pow_f32_i(base, exp) == 1.0f32),
        (exp == 1) ==> (pow_f32_i(base, exp) == base),
        (exp > 1) ==> (pow_f32_i(base, exp) == base.spec_mul(pow_f32_i(base, exp - 1))),
{
    if exp == 0 {
        1.0f32
    } else if exp == 1 {
        base
    } else {
        base * pow_f32_i(base, exp - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn chebvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires deg >= 0,
    ensures

        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg + 1),
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,

        deg >= 1 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x@[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): This block was not part of the current issue. The previous fixes related to type casting (int to usize) and `get_unchecked` for vector access were already implemented to address earlier verification errors. No changes are required in this iteration based on the provided errors. */
{
    let n = x.len();
    let mut result = Vec::new();
    result.reserve(n);

    if deg == 0 {
        let mut i = 0;
        while i < n
            invariant
                0 <= i && i <= n,
                result.len() == i,
                result.capacity() == n,
                forall|j: int| 0 <= j && (j as usize) < i ==> result.view()[j as usize].len() == 1,
                forall|j: int| 0 <= j && (j as usize) < i ==> result.view()[j as usize][0] == 1.0f32,

        {
            let mut row = Vec::new();
            row.push(1.0f32);
            result.push(row);
            i = i + 1;
        }
        return result;
    }

    let mut i = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            result.len() == i,
            result.capacity() == n,
            forall|j: int| 0 <= j && (j as usize) < i ==> result.view()[j as usize].len() == (deg + 1),
            forall|j: int| 0 <= j && (j as usize) < i ==> result.view()[j as usize][0] == 1.0f32,
            deg >= 1 ==> forall|j: int| 0 <= j && (j as usize) < i ==> result.view()[j as usize][1] == x.view()[j as usize],

    {
        let mut row = Vec::new();
        row.reserve(deg + 1);

        row.push(1.0f32);
        if deg >= 1 {
            row.push(x.get_unchecked(i as usize));
        }

        let mut j = 2;
        while j <= deg
            invariant
                2 <= j && j <= deg + 1,
                row.len() == j,
                row.capacity() == deg + 1,
                row.view()[0] == 1.0f32,
                (deg >= 1) ==> (row.view()[1] == x.view()[i as usize]),
                forall|k: int| 2 <= k && (k as usize) < j ==> row.view()[k as usize] == 2.0f32 * x.view()[i as usize] * row.view()[(k - 1) as usize] - row.view()[(k - 2) as usize],

        {
            let val_k_minus_1 = *row.get_unchecked((j - 1) as usize);
            let val_k_minus_2 = *row.get_unchecked((j - 2) as usize);
            let val_x_i = *x.get_unchecked(i as usize);
            let next_val = 2.0f32 * val_x_i * val_k_minus_1 - val_k_minus_2;
            row.push(next_val);
            j = j + 1;
        }

        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}