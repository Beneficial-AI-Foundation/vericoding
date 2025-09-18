// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed syntax and added GCD helper functions */
spec fn gcd(a: int, b: int) -> int
    decreases int_abs(a) + int_abs(b)
{
    if a == 0 && b == 0 {
        0
    } else if a == 0 {
        int_abs(b)
    } else if b == 0 {
        int_abs(a)
    } else if int_abs(a) >= int_abs(b) {
        gcd(int_abs(b), int_abs(a) % int_abs(b))
    } else {
        gcd(int_abs(a), int_abs(b) % int_abs(a))
    }
}

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

exec fn int_abs_exec(x: i32) -> (result: i32)
    ensures result as int == int_abs(x as int),
    ensures result >= 0
{
    if x >= 0 { x } else { -x }
}

exec fn gcd_exec(a: i32, b: i32) -> (result: i32)
    decreases int_abs(a as int) + int_abs(b as int),
    ensures result as int == gcd(a as int, b as int),
    ensures result >= 0
{
    let a_abs = int_abs_exec(a);
    let b_abs = int_abs_exec(b);
    if a_abs == 0 && b_abs == 0 {
        0
    } else if a_abs == 0 {
        b_abs
    } else if b_abs == 0 {
        a_abs
    } else if a_abs >= b_abs {
        gcd_exec(b_abs, a_abs % b_abs)
    } else {
        gcd_exec(a_abs, b_abs % a_abs)
    }
}
// </vc-helpers>

// <vc-spec>
spec fn gcd(a: int, b: int) -> int 
decreases int_abs(a) + int_abs(b), 

{
    if a == 0 && b == 0 {
        0
    } else if a == 0 {
        int_abs(b)
    } else if b == 0 {
        int_abs(a)
    } else if int_abs(a) >= int_abs(b) {
        gcd(int_abs(b), int_abs(a) % int_abs(b))
    } else {
        gcd(int_abs(a), int_abs(b) % int_abs(a))
    }
}


spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn numpy_gcd(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == gcd(#[trigger] x1[i] as int, #[trigger]  x2[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> gcd(#[trigger] x1[i] as int, x2[i] as int) == gcd(#[trigger] int_abs(x1[i] as int), #[trigger] int_abs(x2[i] as int)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == 0 && x2[i] == 0) ==> #[trigger] result[i] == 0,
        forall|i: int| 0 <= i < result.len() ==> (x1[i] != 0 && x2[i] == 0) ==> #[trigger] result[i] as int == int_abs(x1[i] as int),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == 0 && x2[i] != 0) ==> #[trigger] result[i] as int == int_abs(x2[i] as int),
        forall|i: int| 0 <= i < result.len() ==> (result[i] as int) % (x1[i] as int) == 0 && (result[i] as int) % (x2[i] as int) == 0,
        forall|i: int, d: int| 0 <= i < result.len() 
            ==>  (d % (x1[i] as int) == 0 && d % (x2[i] as int) == 0) ==> #[trigger] (d % (result[i] as int)) == 0,
        forall|i: int| 0 <= i < result.len() ==> gcd(x2[i] as int, #[trigger] x1[i] as int) == gcd(x1[i] as int, #[trigger] x2[i] as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Implemented numpy_gcd body with loop and basic proof */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == gcd(x1@[j] as int, x2@[j] as int),
            forall|j: int| 0 <= j < i ==> result@[j] >= 0
    {
        let g = gcd_exec(x1@[i], x2@[i]);
        result.push(g);
        i = i + 1;
    }
    proof {
        assert forall|i: int| 0 <= i < result.len() implies result@[i] as int == gcd(x1@[i] as int, x2@[i] as int) by {
        }
    }
    result
}
// </vc-code>

}
fn main() {}