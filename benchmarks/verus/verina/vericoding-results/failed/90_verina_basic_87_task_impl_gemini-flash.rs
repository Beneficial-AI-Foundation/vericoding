// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result[i] <= result[j],
        result@ =~= a@,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed syntax error in inner loop invariant. */
{
    let mut arr = a.clone();
    let n = arr.len();

    if n == 0 {
        return arr;
    }

    let mut i = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            arr.len() == n,
            forall|x: int, y: int| 0 <= x < y < i as int ==> arr[x as usize] <= arr[y as usize],
            forall|x: int, y: int| 0 <= x < i as int && i as int <= y < n as int ==> arr[x as usize] <= arr[y as usize],
            arr@ =~= a@,
    {
        let mut min_idx = i;
        let mut j = i + 1;
        while j < n
            invariant
                0 <= i as int,
                0 < j as int,
                j as int <= n as int,
                arr.len() == n,
                forall|x: int, y: int| 0 <= x < y < i as int ==> arr[x as usize] <= arr[y as usize],
                forall|x: int, y: int| 0 <= x < i as int && i as int <= y < n as int ==> arr[x as usize] <= arr[y as usize],
                i <= min_idx < n,
                forall|k: int| i as int <= k < j as int ==> arr[min_idx as usize] <= arr[k as usize],
                arr@ =~= a@,
        {
            if arr[j] < arr[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }

        if min_idx != i {
            let temp = arr[i];
            arr.set(i, arr[min_idx]);
            arr.set(min_idx, temp);
        }
        i = i + 1;
    }
    arr
}
// </vc-code>

}
fn main() {}