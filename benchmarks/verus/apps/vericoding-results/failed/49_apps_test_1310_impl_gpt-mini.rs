// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn xor_range(arr: Seq<u32>, i: int, j: int) -> u32;

spec fn valid_input(arr: Seq<u32>) -> bool {
    arr.len() > 0
}

spec fn is_max_xor_subarray(arr: Seq<u32>, result: u32) -> bool
    recommends valid_input(arr)
{
    exists|i: int, j: int| 0 <= i <= j < arr.len() && result == xor_range(arr, i, j) &&
    forall|i1: int, j1: int| 0 <= i1 <= j1 < arr.len() ==> 
        (xor_range(arr, i1, j1) as int) <= (result as int)
}
// </vc-preamble>

// <vc-helpers>
spec fn xor_range(arr: Seq<u32>, i: int, j: int) -> u32
    decreases j - i
{
    if i == j { arr@[i] } else { xor_range(arr, i, j-1) ^ arr@[j] }
}
// </vc-helpers>

// <vc-spec>
fn solve(arr: Vec<u32>) -> (result: u32)
    requires valid_input(arr@)
    ensures is_max_xor_subarray(arr@, result)
// </vc-spec>
// <vc-code>
{
    let n: nat = arr@.len();
    let mut best: u32 = arr.get(0).unwrap().clone();
    let mut best_i: nat = 0;
    let mut best_j: nat = 0;
    let mut i: nat = 0;
    while i < n
        invariant
            i <= n,
            0 <= best_i && best_i <= best_j && best_j < n,
            best == xor_range(arr@, best_i as int, best_j as int),
            forall|a: int, b: int| 0 <= a <= b < (n as int) && (a as nat) < i ==> (xor_range(arr@, a, b) as int) <= (best as int),
        decreases n - i
    {
        let mut cur: u32 = 0;
        let mut j: nat = i;
        while j < n
            invariant
                i <= j + 1,
                if j == i { cur == 0 } else { cur == xor_range(arr@, i as int, (j as int) - 1) },
            decreases n - j
        {
            let val: u32 = arr.get(j as usize).unwrap().clone();
            cur = cur ^ val;
            if (cur as int) > (best as int) {
                best = cur;
                best_i = i;
                best_j = j;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    best
}
// </vc-code>


}

fn main() {}