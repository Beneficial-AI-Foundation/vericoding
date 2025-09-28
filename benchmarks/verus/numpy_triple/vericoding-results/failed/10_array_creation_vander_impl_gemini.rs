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
/* helper modified by LLM (iteration 2): [unchanged from previous turn] */
fn compute_power(base: i8, exp: usize) -> (result: i8)
    requires
        pow_int(base as int, exp as nat) >= i8::MIN as int,
        pow_int(base as int, exp as nat) <= i8::MAX as int,
    ensures
        result as int == pow_int(base as int, exp as nat),
    decreases exp
{
    if exp == 0 {
        1
    } else {
        let prev = compute_power(base, exp - 1);
        base * prev
    }
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
    /* code modified by LLM (iteration 2): [fixed type mismatches in invariants by adding casts] */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i as nat <= x@.len(),
            result@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> result@[k]@.len() == m as nat,
            forall|k: int, l: int| 0 <= k < i as int && 0 <= l < m as int ==>
                result@[k]@[l] as int == pow_int(x@[k] as int, ((m as int) - 1 - l) as nat),
        decreases x.len() - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                (i as nat) < x@.len(),
                m > 0,
                j <= m,
                row@.len() == j as nat,
                forall|l: int| 0 <= l < j as int ==>
                    row@[l] as int == pow_int(x@[i as int] as int, ((m as int) - 1 - l) as nat),
            decreases m - j
        {
            let exp = m - 1 - j;
            let val = compute_power(x[i], exp);
            row.push(val);
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