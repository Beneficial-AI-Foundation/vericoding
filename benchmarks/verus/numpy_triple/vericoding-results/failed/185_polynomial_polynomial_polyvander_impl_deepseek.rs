// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_pow_one(n: nat)
    ensures
        pow(1.0f32, n) == 1.0f32,
{
    if n == 0 {
    } else {
        lemma_pow_one((n - 1) as nat);
    }
}

proof fn lemma_pow_zero()
    ensures
        pow(0.0f32, 0) == 1.0f32,
{
}

/* helper modified by LLM (iteration 5): fixed f32 multiplication using native arithmetic */
spec fn pow(base: f32, exponent: nat) -> f32
    decreases exponent,
{
    if exponent == 0 {
        1.0f32
    } else {
        base * pow(base, (exponent - 1) as nat)
    }
}

// </vc-helpers>

// <vc-spec>
fn polyvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed index access and type casting issues */
    let mut result = Vec::<Vec<f32>>::new();
    let n = x.len();
    let d = deg;
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].len() == d + 1,
            forall|j: int| 0 <= j < i ==> result[j][0] == 1.0f32,
            d > 0 ==> forall|j: int| 0 <= j < i ==> result[j][1] == (x@)[j],
    {
        let mut row = Vec::<f32>::new();
        let mut j: usize = 0;
        while j <= d
            invariant
                j <= d + 1,
                row.len() == j,
                forall|k: int| 0 <= k < j ==> row[k] == pow(x@[i as int], k as nat),
        {
            if j == 0 {
                row.push(1.0f32);
            } else {
                let val = x[i] * row[j - 1];
                row.push(val);
            }
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