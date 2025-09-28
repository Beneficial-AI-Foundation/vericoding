// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `can_add` function was intended to return an `i8` type. The previous implementation returned `int`, leading to a type mismatch. The fix involves casting `a + b` explicitly to `i8` ensuring the return type is correct without changing the logic. */
proof fn can_add(a: i8, b: i8) -> (c: i8)
    requires
        (a as int + b as int) >= i8::MIN as int,
        (a as int + b as int) <= i8::MAX as int,
    ensures
        c as int == a as int + b as int
{
    (a + b) as i8
}
// </vc-helpers>

// <vc-spec>
fn add(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == x1[i] as int + x2[i] as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error where `get_unchecked` returns a reference (`&i8`) but `can_add` expects a value (`i8`). The fix involves dereferencing the return value of `get_unchecked` using `*` when calling `can_add`. Also fixed indexing of `result`, `x1`, and `x2` to use `usize` instead of `int` in the `forall` invariant to resolve slice indexing errors. */
{
    let mut result: Vec<i8> = Vec::new();
    let len = x1.len();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j as usize] as int == x1.get_unchecked(j as usize) as int + x2.get_unchecked(j as usize) as int,
        decreases len - i
    {
        // Prove that the addition will not overflow or underflow
        proof {
            assert((x1.get_unchecked(i) as int + x2.get_unchecked(i) as int) >= i8::MIN as int);
            assert((x1.get_unchecked(i) as int + x2.get_unchecked(i) as int) <= i8::MAX as int);
        }
        let sum = can_add(*x1.get_unchecked(i), *x2.get_unchecked(i));
        result.push(sum);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}