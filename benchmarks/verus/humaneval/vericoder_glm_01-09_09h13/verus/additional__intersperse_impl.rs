use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    if numbers.len() == 0 {
        return Vec::new();
    }
    let mut res = Vec::new();
    res.push(numbers[0]);
    let mut i = 1;
    while i < numbers.len()
        invariant
            1 <= i <= numbers.len(),
            res.len() == 2 * i - 1,
            forall|j: int| 0 <= j < res.len() && j % 2 == 0 ==> #[trigger] res[j] == numbers[j / 2],
            forall|j: int| 0 <= j < res.len() && j % 2 == 1 ==> #[trigger] res[j] == delim
        decreases numbers.len() - i,
    {
        res.push(delim);
        res.push(numbers[i]);
        i += 1;
    }
    res
}
// </vc-code>

fn main() {}
}