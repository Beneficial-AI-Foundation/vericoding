// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no-op proof helper for vectors */
proof fn vec_len_nonneg<T>(_v: &Vec<T>) {
    assert(true);
}

// </vc-helpers>

// <vc-spec>
fn unique_sorted(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() <= arr.len(),
        forall|i: int| 0 <= i < result.len() - 1 ==> #[trigger] result[i] <= result[i + 1],
        forall|x: i32| arr@.contains(x) <==> result@.contains(x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build sorted unique vector without proof block */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            res.len() <= arr.len(),
            forall|k: int| k + 1 < (res.len() as int) ==> #[trigger] res[k] <= res[k + 1],
            forall|y: i32| res@.contains(y) <==> (exists|j: int| j < (i as int) && arr[j] == y),
        decreases arr.len() - i
    {
        let x = arr[i];

        let mut j: usize = 0;
        let mut found: bool = false;
        while j < res.len()
            invariant
                j <= res.len(),
                (exists|k: int| k < (j as int) && res[k] == x) ==> found,
                !found ==> (forall|k: int| k < (j as int) ==> res[k] != x),
            decreases res.len() - j
        {
            if res[j] == x {
                found = true;
                break;
            }
            j = j + 1;
        }

        if !found {
            let mut p: usize = 0;
            while p < res.len()
                invariant p <= res.len(),
                decreases res.len() - p
            {
                if res[p] >= x {
                    break;
                }
                p = p + 1;
            }
            res.insert(p, x);
        }

        i = i + 1;
    }

    // Verification assertions (not in a proof block)
    assert(forall|y: i32| res@.contains(y) <==> (exists|j: int| j < (arr.len() as int) && arr[j] == y));
    assert(forall|y: i32| res@.contains(y) <==> arr@.contains(y));
    assert(res.len() <= arr.len());
    assert(forall|k: int| k + 1 < (res.len() as int) ==> res[k] <= res[k + 1]);

    res
}

// </vc-code>

}
fn main() {}