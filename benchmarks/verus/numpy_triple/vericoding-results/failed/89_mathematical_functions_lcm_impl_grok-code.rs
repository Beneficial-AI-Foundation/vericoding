// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax errors in ensures clauses and added correct ensures for gcd and lcm values */
spec fn gcd_spec(a: int, b: int) -> nat
    requires a >= 0, b >= 0
    decreases b
{
    if b == 0 { a as nat } else { gcd_spec(b, a % b) }
}

spec fn lcm_spec(a: int, b: int) -> nat
    requires a >= 0, b >= 0
{
    if a == 0 || b == 0 { 0 as nat } else { ((a as nat * b as nat) / gcd_spec(a, b)) as nat }
}

exec fn gcd(mut a: i64, mut b: i64) -> i64
    requires 0 <= a, 0 <= b
    ensures 0 <= result
    ensures result == gcd_spec(a as int, b as int) as i64
    decreases b
{
    if b == 0 {
        a
    } else {
        while a % b != 0
            invariant 0 <= a, 0 <= b, gcd_spec(a as int, b as int) == gcd_spec(#[trigger] a as int, #[trigger] b as int)
        {
            let temp = a % b;
            a = b;
            b = temp;
        }
        b
    }
}

exec fn lcm_helper(a: i64, b: i64) -> i64
    requires 0 <= a, 0 <= b
    ensures 0 <= result
    ensures result == lcm_spec(a as int, b as int) as i64
{
    if a == 0 || b == 0 {
        0
    } else {
        let g = gcd(a, b);
        (a / g) * b
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
/* code modified by LLM (iteration 5): Fixed syntax error in loop increment */
{
    let len = x1.len();
    let mut result = Vec::<i32>::new();
    let mut i = 0;
    while i < len
        invariant
            result.len() == i,
            i <= len,
            forall|j: int| 0 <= j < i ==> result@[j] >= 0,
            forall|j: int| 0 <= j < i ==> (x1@[j] == 0 || x2@[j] == 0) ==> result@[j] == 0,
            forall|j: int| 0 <= j < i ==> (x1@[j] != 0 && x2@[j] != 0) ==> result@[j] > 0
        decreases len - i
    {
        let a_i32 = if x1[i] < 0 { -x1[i] } else { x1[i] };
        let b_i32 = if x2[i] < 0 { -x2[i] } else { x2[i] };
        proof {
            assert(a_i32 >= 0);
            assert(b_i32 >= 0);
        }
        let l_val_i64 = lcm_helper(a_i32 as i64, b_i32 as i64);
        let l_val = l_val_i64 as i32;
        result.push(l_val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}