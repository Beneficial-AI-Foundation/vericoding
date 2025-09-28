// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(arr: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j]
}

spec fn has_decrease_at(arr: Seq<int>, i: int) -> bool {
    1 <= i < arr.len() && arr[i] < arr[i-1]
}

spec fn is_largest_decrease_index(arr: Seq<int>, result: int) -> bool {
    has_decrease_at(arr, result) && 
    (forall|j: int| #[trigger] arr.index(j) >= 0 && result < j < arr.len() ==> arr.index(j) >= arr.index(j-1))
}

spec fn is_non_decreasing(arr: Seq<int>) -> bool {
    forall|i: int| #[trigger] arr.index(i) >= 0 && 1 <= i < arr.len() ==> arr.index(i) >= arr.index(i-1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn can_arrange(arr: Vec<i8>) -> (result: i8)
    requires 
        valid_input(arr@),
    ensures 
        result == -1 || (0 < result as int && result as int < arr.len()),
        result == -1 ==> is_non_decreasing(arr@),
        result != -1 ==> is_largest_decrease_index(arr@, result as int),
        result != -1 ==> (exists|i: int| has_decrease_at(arr@, i)),
// </vc-spec>
// <vc-code>
{
    let n = arr.len();
    if n <= 1 {
        return -1;
    }

    let mut i: usize = 1;
    let mut last_dec: int;
    proof { last_dec = -1; }

    while i < n
        invariant
            1 <= i as int && i as int <= n as int,
            -1 <= last_dec,
            last_dec == -1 || 1 <= last_dec && last_dec < i as int,
            forall|j: int| 1 <= j && j < i as int && j > last_dec ==> arr@[j] >= arr@[j-1],
            last_dec == -1 || arr@[last_dec] < arr@[last_dec - 1],
        decreases n as int - i as int
    {
        let p = arr[i - 1];
        let c = arr[i];
        if c < p {
            let k = i;
            i += 1;
            proof { last_dec = k as int; }
        } else {
            i += 1;
        }
    }

    if last_dec == -1 {
        return -1;
    } else {
        let r: i8 = last_dec as i8;
        return r;
    }
}
// </vc-code>


}

fn main() {}