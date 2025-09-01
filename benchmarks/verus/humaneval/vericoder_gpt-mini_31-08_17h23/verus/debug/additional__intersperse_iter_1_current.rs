use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
{
    // impl-start
    let n = numbers.len();
    if n == 0 {
        Vec::new()
    } else {
        let mut res: Vec<i32> = Vec::with_capacity(2 * n - 1);
        let mut i: nat = 0;
        while i < n - 1 {
            invariant(i <= n - 1);
            invariant(res.len() == 2 * i);
            invariant(forall|j: int| 0 <= j && j < res.len() && j % 2 == 0 ==> #[trigger] res[j] == numbers[j / 2]);
            invariant(forall|j: int| 0 <= j && j < res.len() && j % 2 == 1 ==> #[trigger] res[j] == delim);
            res.push(numbers[i]);
            res.push(delim);
            i = i + 1;
        }
        res.push(numbers[n - 1]);
        res
    }
    // impl-end
}
// </vc-code>

fn main() {}
}