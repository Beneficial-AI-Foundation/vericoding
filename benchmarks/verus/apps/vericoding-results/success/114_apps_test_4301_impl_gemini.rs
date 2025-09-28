// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max_of_seq(s: Seq<int>) -> int
    recommends s.len() >= 1
{
    if s.len() == 1 {
        s[0]
    } else {
        if s[0] >= s[1] {
            s[0]
        } else {
            s[1]
        }
    }
}

spec fn max_excluding(s: Seq<int>, exclude_idx: int) -> int
    recommends 0 <= exclude_idx < s.len() && s.len() >= 2
{
    if exclude_idx == 0 {
        max_of_seq(s.subrange(1, s.len() as int))
    } else if exclude_idx == s.len() - 1 {
        max_of_seq(s.subrange(0, s.len() - 1))
    } else {
        max_of_seq(s.subrange(0, exclude_idx).add(s.subrange(exclude_idx + 1, s.len() as int)))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no change needed, error was in the caller */
fn find_max_of_slice(slice: &[i8]) -> (max_val: i8)
    requires
        slice.len() > 0,
    ensures
        exists|k: int| 0 <= k < slice.len() && max_val == slice@.index(k),
        forall|k: int| 0 <= k < slice.len() ==> slice@.index(k) <= max_val,
{
    let mut max_val = slice[0];
    let mut i: usize = 1;

    while i < slice.len()
        invariant
            slice.len() > 0,
            1 <= i <= slice.len(),
            exists|k: int| 0 <= k < i && max_val == slice@.index(k),
            forall|k: int| 0 <= k < i ==> slice@.index(k) <= max_val,
        decreases slice.len() - i
    {
        if slice[i] > max_val {
            max_val = slice[i];
        }
        i = i + 1;
    }
    max_val
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<i8>) -> (result: Vec<i8>)
    requires input@.len() >= 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): simplified temp_vec creation using clone and remove */
    let n = input.len();
    let mut result = Vec::new();
    let mut i: usize = 0;

    let ghost original_input = input@;

    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            input.len() == n,
            input@ == original_input,
            n >= 2, // From function precondition
        decreases n - i
    {
        let mut temp_vec = input.clone();
        temp_vec.remove(i);

        let max_val = find_max_of_slice(temp_vec.as_slice());
        result.push(max_val);
        i = i + 1;
    }

    result
}
// </vc-code>


}

fn main() {}