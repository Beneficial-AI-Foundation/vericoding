// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proof that abs_diff is non-negative */
proof fn abs_diff_nonneg(a: int, b: int)
    ensures
        abs_diff(a,b) >= 0,
{
    if a >= b {
        assert(a - b >= 0);
    } else {
        assert(b - a >= 0);
    }
}

/* helper modified by LLM (iteration 5): proof that abs_diff equals i32 absolute difference */
proof fn abs_diff_equiv_i32(a: i32, b: i32)
    ensures
        abs_diff(a as int, b as int) == (a - b).abs() as int,
{
    let d: i32 = a - b;
    if (a as int) >= (b as int) {
        assert(abs_diff(a as int, b as int) == (a as int) - (b as int));
        assert((d as int) == (a as int) - (b as int));
        assert(d.abs() as int == (d as int));
        assert(abs_diff(a as int, b as int) == d.abs() as int);
    } else {
        assert(abs_diff(a as int, b as int) == (b as int) - (a as int));
        assert(((-d) as int) == (b as int) - (a as int));
        assert(d.abs() as int == ((-d) as int));
        assert(abs_diff(a as int, b as int) == d.abs() as int);
    }
}

// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: &Vec<i32>, threshold: i32) -> (result: bool)
    requires threshold >= 0,
    ensures
        !result <==> (forall|i: int, j: int| 
            0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j ==> 
            abs_diff(numbers[i] as int, numbers[j] as int) >= threshold as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): nested loops using sequence indexing (numbers@) in invariants and runtime abs for i32 */
    let n: usize = numbers.len();
    let mut i: usize = 0;
    let mut found: bool = false;
    while i < n && !found
        invariant
            i <= n,
            !found ==> forall|p: int, q: int|
                0 <= p && p < (i as int) && 0 <= q && q < (n as int) && p < q ==>
                abs_diff(numbers@[p] as int, numbers@[q] as int) >= (threshold as int),
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n && !found
            invariant
                i <= n,
                j <= n,
                !found ==> forall|p: int, q: int|
                    0 <= p && p < (i as int) && 0 <= q && q < (n as int) && p < q ==>
                    abs_diff(numbers@[p] as int, numbers@[q] as int) >= (threshold as int),
                !found ==> forall|q: int|
                    (i as int) < q && q < (j as int) ==>
                    abs_diff(numbers@[i as int] as int, numbers@[q] as int) >= (threshold as int),
            decreases n - j
        {
            let diff: i32 = (numbers[i] - numbers[j]).abs();
            if diff < threshold {
                found = true;
            } else {
                j += 1;
            }
        }
        i += 1;
    }
    found
}

// </vc-code>

}
fn main() {}