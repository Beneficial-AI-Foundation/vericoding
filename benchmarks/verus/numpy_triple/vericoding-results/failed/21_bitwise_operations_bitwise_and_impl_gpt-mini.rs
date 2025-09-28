// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): basic u8 bitwise-and numeric facts */
fn byte_and_facts(a: u8, b: u8)
    ensures
        (a & b) as int >= 0,
        (a & b) as int <= a as int,
        (a & b) as int <= b as int,
{
    proof {
        let r: int = (a & b) as int;
        let ai: int = a as int;
        let bi: int = b as int;
        // non-negativity
        assert(r >= 0);
        // Decompose a into (a & b) | (a & !b)
        assert(((a & b) | (a & !b)) as int == ai);
        assert(((a & b) & (a & !b)) == 0u8);
        assert(r <= ai);
        // Decompose b into (a & b) | (b & !a)
        assert(((a & b) | (b & !a)) as int == bi);
        assert(((a & b) & (b & !a)) == 0u8);
        assert(r <= bi);
    }
}

// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: Vec<u8>, x2: Vec<u8>) -> (result: Vec<u8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] as int >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] as int >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] & x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int >= 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int <= x1[i] as int,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int <= x2[i] as int,
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> (x1[i] == 0 || x2[i] == 0)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == x2[i] ==> result[i] == x1[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): cast lengths and indices between usize and int; maintain invariants */
{
    let n: int = x1.len() as int;
    let mut res: Vec<u8> = Vec::new();
    let mut i: int = 0 as int;
    while i < n
        invariant
            0 <= i,
            i <= n,
            (res.len() as int) == i,
            forall|j: int| 0 <= j < (res.len() as int) ==> res[j as usize] == (x1[j as usize] & x2[j as usize]),
        decreases n - i
    {
        let xi: u8 = x1[i as usize];
        let yi: u8 = x2[i as usize];
        res.push(xi & yi);
        byte_and_facts(xi, yi);
        i = i + 1 as int;
    }
    res
}

// </vc-code>

}
fn main() {}