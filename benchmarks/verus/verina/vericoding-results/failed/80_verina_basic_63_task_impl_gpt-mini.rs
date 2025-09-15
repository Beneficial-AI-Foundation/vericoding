// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-preamble>

// <vc-helpers>
spec fn within_bounds(n: int, i: int) -> bool { 0 <= i && i < n }
proof fn witness_yields_exists(numbers: &Vec<i32>, n: int, i: int, j: int, threshold: int)
    requires n == numbers.len() as int,
    requires 0 <= i && i < n && 0 <= j && j < n && i != j && abs_diff(numbers[i as usize] as int, numbers[j as usize] as int) < threshold,
    ensures exists|ii: int, jj: int| 0 <= ii && ii < n && 0 <= jj && jj < n && ii != jj && abs_diff(numbers[ii as usize] as int, numbers[jj as usize] as int) < threshold
{
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
    let n = numbers.len();
    let n_i: int = n as int;
    let mut res: bool = false;
    let mut found_i: int = -1;
    let mut found_j: int = -1;

    let mut i: int = 0;
    while i < n_i
        invariant 0 <= i && i <= n_i
        invariant forall|i0: int, j0: int| 0 <= i0 < i && 0 <= j0 && j0 < n_i && i0 != j0 ==> res || abs_diff(numbers[i0 as usize] as int, numbers[j0 as usize] as int) >= threshold as int
        decreases n_i - i
    {
        let mut j: int = i + 1;
        while j < n_i
            invariant i + 1 <= j && j <= n_i
            invariant forall|j0: int| i + 1 <= j0 && j0 < j ==> res || abs_diff(numbers[i as usize] as int, numbers[j0 as usize] as int) >= threshold as int
            decreases n_i - j
        {
            if abs_diff(numbers[i as usize] as int, numbers[j as usize] as int) < threshold as int {
                res = true;
                found_i = i;
                found_j = j;
                break;
            }
            j += 1;
        }
        if res { break; }
        i += 1;
    }

    proof {
        if (!res) {
            // From the outer invariant at i == n_i and res == false we get the universal property
            assert(forall|i0: int, j0: int| 0 <= i0 < n_i && 0 <= j0 && j0 < n_i && i0 != j0 ==>
                abs_diff(numbers[i0 as usize] as int, numbers[j0 as usize] as int) >= threshold as int);
        } else {
            // Use recorded witness to produce existence
            assert(0 <= found_i && found_i < n_i);
            assert(0 <= found_j && found_j < n_i);
            assert(found_i != found_j);
            assert(abs_diff(numbers[found_i as usize] as int, numbers[found_j as usize] as int) < threshold as int);
            assert(exists|ii: int, jj: int| 0 <= ii && ii < n_i && 0 <= jj && jj < n_i && ii != jj && abs_diff(numbers[ii as usize] as int, numbers[jj as usize] as int) < threshold as int);
        }
    }

    res
}

// </vc-code>

}
fn main() {}