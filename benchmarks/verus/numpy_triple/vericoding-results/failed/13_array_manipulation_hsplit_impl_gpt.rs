// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple spec helpers for chunk sizing and indexing */
pub open spec fn chunk_len(n: nat, k: nat) -> nat { if k > 0 { n / k } else { 0 } }

/* helper modified by LLM (iteration 2): spec helper to compute the linearized index */
pub open spec fn chunk_index(part_idx: int, part_len: int, elem_idx: int) -> int { part_idx * part_len + elem_idx }
// </vc-helpers>

// <vc-spec>
fn hsplit(arr: Vec<f32>, k: usize) -> (result: Vec<Vec<f32>>)
    requires 
        k > 0,
        arr@.len() % (k as nat) == 0,
    ensures
        result@.len() == k,
        forall|part_idx: int| 0 <= part_idx < k as int ==> result@[part_idx].len() == arr@.len() / (k as nat),
        forall|part_idx: int, elem_idx: int| 
            0 <= part_idx < k as int && 0 <= elem_idx < (arr@.len() / (k as nat)) as int ==>
            #[trigger] result@[part_idx][elem_idx] == arr@[part_idx * ((arr@.len() / (k as nat)) as int) + elem_idx],
        forall|i: int| 0 <= i < arr@.len() ==> 
            exists|p: int, e: int| 
                0 <= p < k as int && 0 <= e < (arr@.len() / (k as nat)) as int &&
                i == p * ((arr@.len() / (k as nat)) as int) + e &&
                #[trigger] arr@[i] == result@[p][e]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement hsplit by constructing chunks sequentially; avoid usize multiplication overflow by tracking a running start index; maintain invariants linking exec-level vectors to spec-level properties */
    let n: usize = arr.len();
    let part_len: usize = n / k;

    // Spec-level connections
    assert(arr@.len() == n as nat);
    assert((arr@.len() / (k as nat)) == part_len as nat);

    let mut res: Vec<Vec<f32>> = Vec::new();
    let mut p: usize = 0;
    let mut start: usize = 0; // start index in arr for current part

    while p < k
        invariant
            k > 0,
            arr@.len() % (k as nat) == 0,
            res@.len() == p as nat,
            // Each completed part has the correct length
            forall|part_idx: int| 0 <= part_idx < p as int ==> res@[part_idx].len() == arr@.len() / (k as nat),
            // Mapping property for completed parts
            forall|part_idx: int, elem_idx: int|
                0 <= part_idx < p as int && 0 <= elem_idx < (arr@.len() / (k as nat)) as int ==>
                    #[trigger] res@[part_idx][elem_idx] == arr@[part_idx * ((arr@.len() / (k as nat)) as int) + elem_idx],
            // Track the linear start index: start == p * part_len
            start as int == p as int * (part_len as int),
            // Start is within bounds
            start <= n,
            p <= k,
        decreases (k - p) as int
    {
        let mut part: Vec<f32> = Vec::new();
        let mut e: usize = 0;
        while e < part_len
            invariant
                k > 0,
                arr@.len() % (k as nat) == 0,
                res@.len() == p as nat,
                part@.len() == e as nat,
                // Elements copied so far match arr starting at `start`
                forall|elem_idx: int|
                    0 <= elem_idx < e as int ==> #[trigger] part@[elem_idx] == arr@[start as int + elem_idx],
                start as int == p as int * (part_len as int),
                start <= n,
            decreases (part_len - e) as int
        {
            // We copy element at global index idx = start + e
            // Prove no overflow and in-bounds
            assert(e < part_len);
            // From outer invariant with p < k, we have (p + 1) * part_len <= k * part_len <= n
            proof {
                // General division property: (n / k) * k <= n
                assert(((n as nat) / (k as nat)) * (k as nat) <= n as nat);
                // start + part_len <= n (as ints)
                assert(start as int == p as int * (part_len as int));
                assert((p as int + 1) * (part_len as int) <= (k as int) * (part_len as int));
                assert(((k as nat) * (part_len as nat)) <= n as nat);
            }
            let idx: usize = start + e; // safe since idx < n proved below
            // Show idx < n for exec indexing and overflow safety
            assert(start + part_len <= n);
            assert(idx < n);

            let val: f32 = arr[idx];
            part.push(val);

            // Re-establish mapping for indices < e+1
            assert forall|elem_idx: int|
                0 <= elem_idx < e as int + 1 ==> #[trigger] part@[elem_idx] == arr@[start as int + elem_idx]
            by {
                if elem_idx == e as int {
                    // new element just pushed
                    assert(part@[elem_idx] == arr@[start as int + elem_idx]);
                } else {
                    // old elements preserved by push
                    assert(0 <= elem_idx < e as int);
                    assert(part@[elem_idx] == arr@[start as int + elem_idx]);
                }
            };

            e = e + 1;
        }
        // part has expected length and mapping
        assert(part@.len() == part_len as nat);
        assert(part@.len() == arr@.len() / (k as nat));

        res.push(part);

        // After push, establish mapping for the new part at index p
        assert(res@.len() == (p + 1) as nat);
        assert forall|elem_idx: int|
            0 <= elem_idx < (arr@.len() / (k as nat)) as int ==>
                #[trigger] res@[p as int][elem_idx] == arr@[p as int * ((arr@.len() / (k as nat)) as int) + elem_idx]
        by {
            // res@[p] equals the `part` we constructed
            assert(res@[p as int].len() == arr@.len() / (k as nat));
            assert(start as int == p as int * (part_len as int));
            assert((arr@.len() / (k as nat)) as int == part_len as int);
            assert forall|elem_idx2: int|
                0 <= elem_idx2 < (arr@.len() / (k as nat)) as int implies
                    res@[p as int][elem_idx2] == arr@[p as int * (part_len as int) + elem_idx2]
            by {
                if 0 <= elem_idx2 < (arr@.len() / (k as nat)) as int {
                    assert(res@[p as int][elem_idx2] == arr@[start as int + elem_idx2]);
                    assert(start as int == p as int * (part_len as int));
                }
            };
        };

        // Move to next chunk
        assert(start + part_len <= n);
        start = start + part_len;
        p = p + 1;
    }

    // Final properties
    assert(res@.len() == k as nat);
    assert((arr@.len() / (k as nat)) == part_len as nat);

    // The forward mapping is already provided by loop invariant at termination (p == k)
    assert forall|part_idx: int, elem_idx: int|
        0 <= part_idx < k as int && 0 <= elem_idx < (arr@.len() / (k as nat)) as int ==>
            #[trigger] res@[part_idx][elem_idx] == arr@[part_idx * ((arr@.len() / (k as nat)) as int) + elem_idx]
    by { };

    // The backward mapping: each arr index belongs to some (p,e)
    assert forall|i: int| 0 <= i < arr@.len() ==>
        exists|p_i: int, e_i: int|
            0 <= p_i < k as int && 0 <= e_i < (arr@.len() / (k as nat)) as int &&
            i == p_i * ((arr@.len() / (k as nat)) as int) + e_i &&
            #[trigger] arr@[i] == res@[p_i][e_i]
    by {
        if 0 <= i < arr@.len() {
            // part_len > 0 when arr@.len() > 0 (since k > 0 and arr@.len() == k * part_len)
            let plen_i: int = (arr@.len() / (k as nat)) as int;
            assert(plen_i >= 0);
            if plen_i == 0 {
                // If arr is empty, this branch won't execute due to antecedent 0 <= i < 0
            } else {
                let p_i: int = i / plen_i;
                let e_i: int = i % plen_i;
                // Standard div/mod facts
                assert(0 <= e_i < plen_i);
                // From i < k * plen_i, deduce p_i < k
                assert((k as int) * plen_i >= 0);
                assert(i < (k as int) * plen_i);
                assert(p_i < k as int);
                assert(i == p_i * plen_i + e_i);
                // Use the established forward mapping
                assert(res@[p_i][e_i] == arr@[p_i * plen_i + e_i]);
                assert(arr@[i] == res@[p_i][e_i]);
            }
        }
    };

    res
}
// </vc-code>


}
fn main() {}