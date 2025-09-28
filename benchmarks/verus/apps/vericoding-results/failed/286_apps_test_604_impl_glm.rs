// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(arr: Seq<int>) -> bool {
    true
}

spec fn distinct_non_zero_count(arr: Seq<int>) -> int {
    Set::<int>::new(|x: int| arr.contains(x) && x != 0).len() as int
}
// </vc-preamble>

// <vc-helpers>
spec fn vec_to_seq_int(arr: Vec<i8>) -> Seq<int> {
    arr@.map(|i, x| x as int)
}
// </vc-helpers>

// <vc-spec>
fn solve(arr: Vec<i8>) -> (result: i8)
    requires 
        valid_input(vec_to_seq_int(arr))
    ensures 
        result >= 0,
        result as int <= arr@.len(),
        result as int == distinct_non_zero_count(vec_to_seq_int(arr))
// </vc-spec>
// <vc-code>
{
    let mut seen = std::collections::HashSet::new();
    let mut count = 0;
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= arr.len(),
            count == seen.len(),
        decreases arr.len() - i
    {
        let x = arr[i];
        if x != 0 && !seen.contains(&x) {
            seen.insert(x);
            count += 1;
        }
        i += 1;
    }
    count as i8
}
// </vc-code>


}

fn main() {}