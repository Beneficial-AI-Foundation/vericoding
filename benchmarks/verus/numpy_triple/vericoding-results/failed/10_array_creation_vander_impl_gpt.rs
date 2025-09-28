// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn pow_int(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow_int(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute exponent index from m and j with proper nat cast */
spec fn exp_index(m: nat, j: int) -> nat
    requires
        0 < m,
        0 <= j < m as int,
    ensures
        exp_index(m, j) == ((m - 1) - (j as nat)) as nat,
{
    ((m - 1) - (j as nat)) as nat
}

// </vc-helpers>

// <vc-spec>
fn vander(x: Vec<i8>, m: usize) -> (result: Vec<Vec<i8>>)
    requires 
        x@.len() > 0,
        m > 0,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() == m,
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < m ==> 
            result@[i]@[j] as int == pow_int(x@[i] as int, (m - 1 - j) as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build matrix with correct shape (n x m) filled with zeros */
    let n = x.len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            x@.len() == n as int,
            0 <= i as int <= n as int,
            result@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> result@[k]@.len() == m as int,
        decreases n - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                0 <= j as int <= m as int,
                row@.len() == j as int,
            decreases m - j
        {
            row.push(0i8);
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