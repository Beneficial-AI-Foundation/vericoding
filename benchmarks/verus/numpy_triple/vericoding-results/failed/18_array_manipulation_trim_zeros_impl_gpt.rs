// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Represents the trim mode for trim_zeros function */
#[derive(Eq, PartialEq)]
pub enum TrimMode {
    /* Trim zeros from the front of the array only (corresponds to 'f') */
    Front,
    /* Trim zeros from the back of the array only (corresponds to 'b') */
    Back,
    /* Trim zeros from both front and back of the array (corresponds to 'fb', default) */
    Both,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): witness index in original sequence for subrange element */
proof fn witness_subrange_index<T>(s: Seq<T>, start: int, end: int, i: int) -> (j: int)
    requires
        0 <= start <= end <= s.len(),
        0 <= i < end - start,
    ensures
        0 <= j < s.len(),
        s.subrange(start, end)[i] == s[j],
{
    let j0 = start + i;
    assert(0 <= j0);
    assert(j0 < end) by {
        assert(start + i < start + (end - start));
        assert(start + (end - start) == end);
    }
    assert(end <= s.len());
    assert(j0 < s.len());
    assert(s.subrange(start, end)[i] == s[j0]);
    j0
}

/* helper modified by LLM (iteration 2): prove that each element of a subrange comes from the original sequence */
proof fn lemma_subrange_membership<T>(s: Seq<T>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        forall|i: int| 0 <= i < end - start ==> exists|j: int| 0 <= j < s.len() && s.subrange(start, end)[i] == s[j],
{
    assert forall|i: int| 0 <= i < end - start ==> exists|j: int| 0 <= j < s.len() && s.subrange(start, end)[i] == s[j] by {
        let j = witness_subrange_index::<T>(s, start, end, i);
        assert(0 <= j && j < s.len());
        assert(s.subrange(start, end)[i] == s[j]);
    }
}
// </vc-helpers>

// <vc-spec>
fn trim_zeros(arr: Vec<f32>, mode: TrimMode) -> (result: Vec<f32>)
    ensures
        result@.len() <= arr@.len(),
        /* Result contains only elements from the original array */
        forall|i: int| 0 <= i < result@.len() ==> 
            exists|j: int| 0 <= j < arr@.len() && #[trigger] result@[i] == arr@[j],
        /* Basic trimming properties based on mode */
        (mode == TrimMode::Front ==> 
            (result@.len() == 0 || result@[0] != 0.0f32)),
        (mode == TrimMode::Back ==> 
            (result@.len() == 0 || result@[result@.len() - 1] != 0.0f32)),
        (mode == TrimMode::Both ==> 
            (result@.len() == 0 || (result@[0] != 0.0f32 && result@[result@.len() - 1] != 0.0f32)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement trimming using usize indices and construct the result while maintaining specs */
    let n: usize = arr.len();
    let mut s: usize = 0;
    let mut e: usize = n;

    match mode {
        TrimMode::Front => {
            while s < e && arr[s] == 0.0f32
                invariant
                    0 <= s as int <= e as int <= n as int,
                    forall|k: int| 0 <= k < s as int ==> arr@[k] == 0.0f32,
                decreases (e - s) as int
            {
                s = s + 1;
            }
        }
        TrimMode::Back => {
            while s < e && arr[e - 1] == 0.0f32
                invariant
                    0 <= s as int <= e as int <= n as int,
                    forall|k: int| e as int <= k < n as int ==> arr@[k] == 0.0f32,
                decreases (e - s) as int
            {
                e = e - 1;
            }
        }
        TrimMode::Both => {
            while s < e && arr[s] == 0.0f32
                invariant
                    0 <= s as int <= e as int <= n as int,
                    forall|k: int| 0 <= k < s as int ==> arr@[k] == 0.0f32,
                decreases (e - s) as int
            {
                s = s + 1;
            }
            while s < e && arr[e - 1] == 0.0f32
                invariant
                    0 <= s as int <= e as int <= n as int,
                    forall|k: int| e as int <= k < n as int ==> arr@[k] == 0.0f32,
                decreases (e - s) as int
            {
                e = e - 1;
            }
        }
    }

    // Facts about boundary elements after trimming
    if (mode == TrimMode::Front || mode == TrimMode::Both) && s < e {
        assert(arr[s] != 0.0f32);
    }
    if (mode == TrimMode::Back || mode == TrimMode::Both) && s < e {
        assert(arr[e - 1] != 0.0f32);
    }

    let mut res: Vec<f32> = Vec::new();
    let mut i: usize = s;
    while i < e
        invariant
            s as int <= i as int <= e as int,
            res@.len() == i as int - s as int,
            forall|t: int| 0 <= t < i as int - s as int ==> res@[t] == arr@[s as int + t],
        decreases (e - i) as int
    {
        let v = arr[i];
        res.push(v);
        // Establish property for the new last element after the push; i has not yet been incremented.
        proof {
            let old_len: int = i as int - s as int;
            assert(res@.len() == old_len + 1);
            assert(res@[old_len] == v);
            assert(arr@[s as int + old_len] == arr@[i as int]);
            assert(arr@[i as int] == v);
        }
        i = i + 1;
    }

    // Strengthen mode-based postconditions on the resulting vector
    proof {
        if mode == TrimMode::Front || mode == TrimMode::Both {
            if res@.len() > 0 {
                assert(res@[0] == arr@[s as int]);
                assert(arr[s] != 0.0f32);
                assert(res@[0] != 0.0f32);
            }
        }
        if mode == TrimMode::Back || mode == TrimMode::Both {
            if res@.len() > 0 {
                assert(res@.len() == (e as int) - (s as int));
                let last_idx: int = res@.len() - 1;
                assert(0 <= last_idx);
                assert(res@[last_idx] == arr@[s as int + last_idx]);
                assert(s as int + last_idx == e as int - 1) by {
                    assert(last_idx == (e as int - s as int) - 1);
                }
                assert(arr[e - 1] != 0.0f32);
                assert(res@[res@.len() - 1] != 0.0f32);
            }
        }
    }

    res
}
// </vc-code>


}
fn main() {}