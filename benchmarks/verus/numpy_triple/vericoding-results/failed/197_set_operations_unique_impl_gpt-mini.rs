// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): map i8 value to array index */
fn to_idx(v: i8) -> usize {
    (((v as i16) + 128) as usize)
}

/* helper modified by LLM (iteration 5): map array index back to i8 value */
fn from_idx(k: usize) -> i8 {
    (((k as i16) - 128) as i8)
}
// </vc-helpers>

// <vc-spec>
fn unique(arr: Vec<i8>) -> (result: Vec<i8>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result@.len() ==> #[trigger] result@[i] < #[trigger] result@[j],

        forall|i: int| 0 <= i < result@.len() ==> exists|j: int| 0 <= j < arr@.len() && #[trigger] result@[i] == #[trigger] arr@[j],

        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() && i != j ==> #[trigger] result@[i] != #[trigger] result@[j],

        forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < result@.len() && #[trigger] arr@[i] == #[trigger] result@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build a seen-table and emit sorted unique values */
    let mut result: Vec<i8> = Vec::new();
    let mut seen: [bool; 256] = [false; 256];

    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            forall|kk: int| 0 <= kk < 256 ==> (seen[kk as usize] <==> exists|j: int| 0 <= j < i as int && arr@[j] as int == kk - 128),
        decreases arr.len() - i,
    {
        let v = arr.get(i).unwrap();
        let idx = to_idx(*v);
        seen[idx] = true;
        i += 1;
    }

    let mut k: usize = 0;
    while k < 256usize
        invariant
            k <= 256usize,
            forall|r: int| 0 <= r < result@.len() ==> exists|kk: int| 0 <= kk < k as int && result@[r] as int == kk - 128,
            forall|kk: int| 0 <= kk < k as int ==> (seen[kk as usize] ==> exists|r: int| 0 <= r < result@.len() && result@[r] as int == kk - 128),
            forall|p: int, q: int| 0 <= p < q < result@.len() ==> result@[p] < result@[q],
        decreases 256usize - k,
    {
        if seen[k] {
            let v = from_idx(k);
            result.push(v);
            proof {
                let new_idx: int = result@.len() - 1;
                assert((result@[new_idx] as int) == (k as int - 128));
                if new_idx > 0 {
                    assert(exists|kk: int| 0 <= kk < k as int && result@[new_idx - 1] as int == kk - 128);
                    assert((result@[new_idx - 1] as int) < (result@[new_idx] as int));
                }
            }
        }
        k += 1;
    }

    proof {
        assert(forall|i: int| 0 <= i < result@.len() ==> exists|j: int| 0 <= j < arr@.len() && result@[i] == arr@[j]);
        assert(forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < result@.len() && arr@[i] == result@[j]);
        assert(forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j]);
    }

    result
}
// </vc-code>

}
fn main() {}