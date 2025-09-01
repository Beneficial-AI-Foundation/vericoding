use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// Adjusted helpers: none required but keep block for compatibility.
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn intersperse(numbers: &[i32], delim: i32) -> (res: Vec<i32>)
    // post-conditions-start
    ensures
        numbers.len() == 0 ==> res.len() == 0,
        numbers.len() != 0 ==> res.len() == 2 * numbers.len() - 1,
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 0 ==> res[i] == numbers[i / 2],
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 1 ==> res[i] == delim
    // post-conditions-end
// </vc-spec>
// <vc-code>
// <vc-code>
{
    // impl-start
    let n = numbers.len();
    if n == 0 {
        Vec::new()
    } else {
        let mut res: Vec<i32> = Vec::with_capacity(2 * n - 1);
        let mut i: usize = 0;
        while i < n - 1 {
            invariant(i <= n - 1);
            invariant(res.len() == 2 * i);
            invariant(forall|j: int|
                0 <= j && j < (res.len() as int) && j % 2 == 0 ==>
                    #[trigger] res[j as usize] == numbers[(j / 2) as usize]);
            invariant(forall|j: int|
                0 <= j && j < (res.len() as int) && j % 2 == 1 ==>
                    #[trigger] res[j as usize] == delim);
            res.push(numbers[i]);
            res.push(delim);
            i = i + 1;
        }
        // At this point res.len() == 2 * (n - 1)
        res.push(numbers[n - 1]);
        // Now res.len() == 2 * n - 1 and invariants extend to include the final element.
        proof {
            // show the even-indexed elements property:
            assert(forall|k: int|
                0 <= k && k < (res.len() as int) && k % 2 == 0 ==>
                    #[trigger] res[k as usize] == numbers[(k / 2) as usize]);
            // show the odd-indexed (delimiter) property:
            assert(forall|k: int|
                0 <= k && k < (res.len() as int) && k % 2 == 1 ==>
                    #[trigger] res[k as usize] == delim);
            // show length property (for non-empty case):
            assert(res.len() == 2 * n - 1);
        }
        res
    }
    // impl-end
}
// </vc-code>
// </vc-code>

fn main() {}
}