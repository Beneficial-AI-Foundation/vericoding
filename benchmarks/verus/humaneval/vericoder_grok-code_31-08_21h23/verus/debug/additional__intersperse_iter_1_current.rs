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
    let n = numbers.len();
    for i in 0..n {
        res.push(numbers[i]);
        if i != n - 1 {
            res.push(delim);
        }
    }
    proof {
        assert(res.len() == 2 * n - 1);
        let mut j = 0;
        while j < res.len()
            invariant
                j <= res.len(),
                forall|k: int| 0 <= k < j ==> 
                    (k % 2 == 0 ==> res[k] == numbers[k / 2]) &&
                    (k % 2 == 1 ==> res[k] == delim)
        {
            if j % 2 == 0 {
                assert(res[j] == numbers[j / 2]);
            } else {
                assert(res[j] == delim);
            }
            j += 1;
        }
    }
    res
}
// </vc-code>

fn main() {}
}