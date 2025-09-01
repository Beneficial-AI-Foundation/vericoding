use vstd::prelude::*;

verus! {

// <vc-helpers>
// helper block left intentionally empty
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
    let n = numbers.len();
    if n == 0 {
        Vec::new()
    } else {
        let mut res: Vec<i32> = Vec::with_capacity(2 * n - 1);
        let mut i: usize = 0;
        while i < n - 1 {
            invariant(i <= n - 1);
            invariant(res.len() == 2 * i);
            invariant(forall|k: int|
                0 <= k && k < (i as int) ==>
                    #[trigger] res[(2 * k) as usize] == numbers[k as usize]);
            invariant(forall|k: int|
                0 <= k && k < (i as int) ==>
                    #[trigger] res[(2 * k + 1) as usize] == delim);
            res.push(numbers[i]);
            res.push(delim);
            i = i + 1;
        }
        res.push(numbers[n - 1]);
        res
    }
}
// </vc-code>

fn main() {}
}