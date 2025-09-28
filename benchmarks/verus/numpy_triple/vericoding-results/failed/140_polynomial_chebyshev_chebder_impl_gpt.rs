// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_len_sub_one_lt(len: nat)
    requires
        len >= 1,
    ensures
        len - 1 < len,
{
}

// </vc-helpers>

// <vc-spec>
fn chebder(c: Vec<i8>, scl: i8) -> (result: Vec<i8>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() - 1,
        c.len() > 1 ==> result[0] == scl * c[1],
        c.len() > 2 ==> result[1] == scl * 4 * c[2],
        forall|j: int| 2 <= j < result.len() ==>
            result[j as int] == scl * (2 * ((j + 1) as i8)) * c[(j + 1) as int],
// </vc-spec>
// <vc-code>
{
    let n = c.len();
    let mut result: Vec<i8> = Vec::new();
    if n == 1 {
        return result;
    }
    let r0: i8 = scl * c[1];
    result.push(r0);
    if n == 2 {
        return result;
    }
    let r1: i8 = scl * (4 as i8) * c[2];
    result.push(r1);
    let mut j: usize = 2;
    while j < n - 1
        invariant
            n == c.len(),
            n >= 3,
            2 <= j && j <= n - 1,
            result.len() == j as int,
            result.len() >= 2,
            result[0] == scl * c[1],
            result[1] == scl * (4 as i8) * c[2],
            forall|k: int| 2 <= k < j as int ==> result[k as int] == scl * (2 * ((k + 1) as i8)) * c[(k + 1) as int],
        decreases (n - 1) - j
    {
        let coef: i8 = 2 * ((j + 1) as i8);
        let v: i8 = scl * coef * c[j + 1];
        result.push(v);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}