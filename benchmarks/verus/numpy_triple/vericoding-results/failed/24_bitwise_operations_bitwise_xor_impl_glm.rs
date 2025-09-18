// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn xor_nonnegative(a: i32, b: i32)
    requires
        a >= 0,
        b >= 0,
    ensures
        (a ^ b) >= 0
{
}

proof fn xor_with_zero_left(a: i32, b: i32)
    ensures
        a == 0 ==> (a ^ b) == b
{
}

proof fn xor_with_zero_right(a: i32, b: i32)
    ensures
        b == 0 ==> (a ^ b) == a
{
}

proof fn xor_equal(a: i32, b: i32)
    ensures
        a == b ==> (a ^ b) == 0
{
}
// </vc-helpers>

// <vc-spec>
fn bitwise_xor(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] ^ x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == x2[i],
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed comma after decreases clause */
    let n = x1.len();
    let mut result: Vec<i32> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        decreases n - i
        invariant {
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] ^ x2[j]),
            forall|j: int| 0 <= j < i ==> result[j] >= 0,
            forall|j: int| 0 <= j < i && x1[j] == 0 ==> result[j] == x2[j],
            forall|j: int| 0 <= j < i && x2[j] == 0 ==> result[j] == x1[j],
            forall|j: int| 0 <= j < i && x1[j] == x2[j] ==> result[j] == 0,
        }
    {
        let a = x1[i];
        let b = x2[i];
        let c = a ^ b;
        proof {
            xor_nonnegative(a, b);
            xor_with_zero_left(a, b);
            xor_with_zero_right(a, b);
            xor_equal(a, b);
        }
        result.push(c);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}