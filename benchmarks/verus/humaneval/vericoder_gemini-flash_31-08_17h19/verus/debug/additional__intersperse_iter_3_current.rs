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
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    if numbers.len() == 0 {
        return res;
    }

    while i < numbers.len()
        invariant
            0 <= i && i <= numbers.len(),
            res.len() == 2 * i - (if i == 0 { 0 } else { 1 }),
            forall|j: int| 0 <= j && j < res.len() && j % 2 == 0 ==> #[trigger] res[j] == numbers[j / 2],
            forall|j: int| 0 <= j && j < res.len() && j % 2 == 1 ==> #[trigger] res[j] == delim,
    {
        if i > 0 {
            res.push(delim);
        }
        res.push(numbers[i]);
        i = i + 1;
    }

    assert(numbers.len() != 0 ==> res.len() == (2 * numbers.len() as int - 1) as usize);
    assert(forall|j: int| 0 <= j && j < res.len() && j % 2 == 0 ==> res[j] == numbers[j / 2]);
    assert(forall|j: int| 0 <= j && j < res.len() && j % 2 == 1 ==> res[j] == delim);

    res
}
// </vc-code>

fn main() {}
}