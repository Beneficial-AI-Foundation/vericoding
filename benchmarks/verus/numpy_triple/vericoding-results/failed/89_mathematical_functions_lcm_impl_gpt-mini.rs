// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): gcd_nat computes gcd for naturals */
fn gcd_nat(mut a: nat, mut b: nat) -> nat {
    while b != 0
        invariant a >= 0 && b >= 0;
        decreases b;
    {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

/* helper modified by LLM (iteration 5): gcd_i32 wrapper converts i32 to nat and back */
fn gcd_i32(a: i32, b: i32) -> i32 {
    let aa: nat = if a < 0 { (-a) as nat } else { a as nat };
    let bb: nat = if b < 0 { (-b) as nat } else { b as nat };
    let g = gcd_nat(aa, bb);
    g as i32
}

/* helper modified by LLM (iteration 5): lcm_i32 returns least common multiple for i32, non-negative */
fn lcm_i32(a: i32, b: i32) -> i32 {
    if a == 0 || b == 0 {
        0
    } else {
        let aa: nat = if a < 0 { (-a) as nat } else { a as nat };
        let bb: nat = if b < 0 { (-b) as nat } else { b as nat };
        let g = gcd_nat(aa, bb);
        ((aa / g) * bb) as i32
    }
}
// </vc-helpers>

// <vc-spec>
spec fn gcd_spec(a: int, b: int) -> nat;

spec fn lcm_spec(a: int, b: int) -> nat;

fn lcm(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),

        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,

        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,

        forall|i: int| 0 <= i < result.len() ==> 
            (x1[i] == 0 || x2[i] == 0) ==> result[i] == 0,

        forall|i: int| 0 <= i < result.len() ==> 
            (x1[i] != 0 && x2[i] != 0) ==> result[i] > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute elementwise lcm using helpers */
    let n = x1.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant res.len() == i;
        decreases n - i;
    {
        let a = x1[i];
        let b = x2[i];
        let v = lcm_i32(a, b);
        res.push(v);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}