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
/* helper modified by LLM (iteration 5): characterizes largest decrease index up to k */
spec fn largest_decrease_up_to(arr: Seq<int>, res: int, k: int) -> bool {
    0 <= k && k <= arr.len() &&
    (res == -1 ==> forall|i: int| 1 <= i < k ==> arr.index(i) >= arr.index(i-1)) &&
    (res != -1 ==> 1 <= res < k && arr.index(res) < arr.index(res-1) && forall|j: int| 1 <= j < k ==> res >= j || arr.index(j) >= arr.index(j-1))
}

/* helper modified by LLM (iteration 5): lemma preserving property when advancing one index */
proof fn largest_decrease_up_to_step(arr: Seq<int>, res: int, k: int)
    requires
        largest_decrease_up_to(arr, res, k),
        1 <= k && k < arr.len(),
    ensures
        largest_decrease_up_to(arr, if arr.index(k) < arr.index(k-1) { k } else { res }, k + 1),
{
    proof {
        // bounds for k+1
        assert(0 <= k + 1 && k + 1 <= arr.len());
        if arr.index(k) < arr.index(k-1) {
            // new result is k
            assert(1 <= k && k < k + 1);
            // for any j in 1..k, k >= j holds, so the disjunction holds for j < k; for j == k k >= j holds
            assert(forall|j: int| 1 <= j < k + 1 ==> k >= j || arr.index(j) >= arr.index(j-1));
            assert(largest_decrease_up_to(arr, k, k + 1));
        } else {
            // arr[k] >= arr[k-1]
            assert(arr.index(k) >= arr.index(k-1));
            // if res == -1, extend the monotonic property to k
            assert(res == -1 ==> forall|i: int| 1 <= i < k + 1 ==> arr.index(i) >= arr.index(i-1));
            // if res != -1, res < k implies res < k+1 and the forall for j<k+1 holds because for j<k it follows from the hypothesis and for j==k arr[k] >= arr[k-1]
            assert(res != -1 ==> 1 <= res < k + 1 && arr.index(res) < arr.index(res-1) && forall|j: int| 1 <= j < k + 1 ==> res >= j || arr.index(j) >= arr.index(j-1));
            assert(largest_decrease_up_to(arr, res, k + 1));
        }
    }
}

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
/* code modified by LLM (iteration 5): find largest index with a decrease by scanning once and use lemma to maintain invariant */
{
    let n: int = arr.len() as int;
    if n <= 1 {
        -1i8
    } else {
        let mut res: int = -1;
        let mut i: int = 1;
        while i < n
            invariant
                1 <= i && i <= n,
                largest_decrease_up_to(arr@, res, i),
            decreases n - i
        {
            let old_res = res;
            if (arr[i as usize] as int) < (arr[(i - 1) as usize] as int) {
                res = i;
            }
            proof {
                largest_decrease_up_to_step(arr@, old_res, i);
            }
            i = i + 1;
        }
        res as i8
    }
}

// </vc-code>


}

fn main() {}