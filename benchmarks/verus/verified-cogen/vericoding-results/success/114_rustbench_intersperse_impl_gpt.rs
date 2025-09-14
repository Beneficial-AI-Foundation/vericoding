// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): parity predicates retained for readability in invariants */
spec fn is_even(i: int) -> bool { i % 2 == 0 }
spec fn is_odd(i: int) -> bool { i % 2 == 1 }
// </vc-helpers>

// <vc-spec>
fn intersperse(numbers: &[i32], delim: i32) -> (res: Vec<i32>)
    ensures
        numbers.len() == 0 ==> res.len() == 0,
        numbers.len() != 0 ==> res.len() == 2 * numbers.len() - 1,
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 0 ==> res[i] == numbers[i / 2],
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 1 ==> res[i] == delim
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): corrected invariants to establish numbers index bounds and added assertions for slice indexing */
    let n_usize: usize = numbers.len();
    let mut r: Vec<i32> = Vec::new();
    if n_usize == 0 {
        return r;
    }
    proof { assert(numbers@.len() == n_usize as int); }
    r.push(numbers[0]);
    let mut i: usize = 1;
    while i < n_usize
        invariant
            numbers@.len() == n_usize as int,
            1 <= i as int <= n_usize as int,
            r.len() == 2 * (i as int) - 1,
            forall|j: int|
                0 <= j && j < r.len() && j % 2 == 0 ==> 0 <= j/2 && j/2 < numbers@.len() && r@[j] == numbers@[(j / 2)],
            forall|j: int|
                0 <= j && j < r.len() && j % 2 == 1 ==> r@[j] == delim,
        decreases n_usize as int - i as int
    {
        r.push(delim);
        assert((i as int) < numbers@.len());
        r.push(numbers[i]);
        i += 1;
    }
    r
}
// </vc-code>

}
fn main() {}