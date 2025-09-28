// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn idx(v: i8) -> int {
    (v as i16 + 128) as int
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
    /* code modified by LLM (iteration 5): fixed invariants with triggers and simplified logic */
    let mut seen: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k < 256
        invariant
            k <= 256,
            seen@.len() == k as int,
            forall|j: int| 0 <= j < seen@.len() ==> seen@[j] == false,
        decreases 256 - k
    {
        seen.push(false);
        k = k + 1;
    }

    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            seen@.len() == 256,
            forall|v: i8| #[trigger] seen@[idx(v)] == arr@.subrange(0, i as int).contains(v),
        decreases arr.len() - i
    {
        let val = arr[i];
        let val_idx = idx(val) as usize;
        seen.set(val_idx, true);
        i = i + 1;
    }

    let mut result: Vec<i8> = Vec::new();
    let mut v: i16 = -128;
    while v <= 127
        invariant
            -128 <= v <= 128,
            seen@.len() == 256,
            forall|u: i8| #[trigger] seen@[idx(u)] == arr@.contains(u),
            forall|a: int, b: int| 0 <= a < b < result@.len() ==> result@[a] < result@[b],
            forall|x: i8| (x as i16) < v ==> (result@.contains(x) <==> arr@.contains(x)),
            forall|x: i8| result@.contains(x) ==> (x as i16) < v,
        decreases 127 - v
    {
        let v_i8 = v as i8;
        let v_idx = idx(v_i8) as usize;
        if seen[v_idx] {
            result.push(v_i8);
        }
        v = v + 1;
    }

    result
}
// </vc-code>

}
fn main() {}