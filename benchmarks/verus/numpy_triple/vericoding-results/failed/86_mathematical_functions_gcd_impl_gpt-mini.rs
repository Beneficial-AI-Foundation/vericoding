// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): iterative Euclidean gcd for i32 with proof obligations */
fn gcd_i32(a0: i32, b0: i32) -> (result: i32)
    ensures result as int == gcd(a0 as int, b0 as int),
    ensures result >= 0,
    decreases int_abs(a0 as int) + int_abs(b0 as int)
{
    let mut a: i32 = if a0 >= 0 { a0 } else { -a0 };
    let mut b: i32 = if b0 >= 0 { b0 } else { -b0 };
    let oa: i32 = a;
    let ob: i32 = b;
    while b != 0
        invariant 0 <= a && 0 <= b,
        invariant gcd(a as int, b as int) == gcd(oa as int, ob as int),
        decreases b as int
    {
        let r: i32 = a % b;
        a = b;
        b = r;
    }
    proof {
        assert(b == 0);
        assert(gcd(oa as int, ob as int) == gcd(a as int, b as int));
        assert(a as int == int_abs(a as int));
    }
    result = a;
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
    /* code modified by LLM (iteration 5): compute elementwise gcd using gcd_i32 helper */
    let mut res: Vec<i32> = Vec::<i32>::new();
    let mut i: int = 0;
    let len_int: int = x1.len() as int;
    while i < len_int
        invariant 0 <= i && i <= len_int,
        invariant res.len() as int == i,
        invariant forall|j: int| 0 <= j < i ==> res[j as usize] as int == gcd(#[trigger] x1[j as usize] as int, #[trigger] x2[j as usize] as int),
        invariant forall|j: int| 0 <= j < i ==> res[j as usize] >= 0,
        decreases len_int - i
    {
        let idx: usize = i as usize;
        let g: i32 = gcd_i32(x1[idx], x2[idx]);
        res.push(g);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}