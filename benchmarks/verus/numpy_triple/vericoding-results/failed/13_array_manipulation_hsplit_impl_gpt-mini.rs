// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate divisible length to product */
fn div_mul_cancel(len: nat, k: nat)
    requires
        k > 0,
        len % k == 0,
    ensures
        len == (len / k) * k,
{
    proof {
        assert(len == (len / k) * k + len % k);
        assert(len % k == 0);
        assert(len == (len / k) * k);
    }
}

/* helper modified by LLM (iteration 5): decompose index into part and element */
fn index_to_pair(len: nat, k: nat, i: nat)
    requires
        k > 0,
        len % k == 0,
        i < len,
    ensures
        exists|p: nat, e: nat|
            p < k && e < len / k && i == p * (len / k) + e,
{
    proof {
        let m: nat = len / k;
        assert(len == m * k);
        assert(i < len);
        assert(len > 0);
        assert(m > 0);
        let p: nat = i / m;
        let e: nat = i % m;
        assert(i == p * m + e);
        assert(e < m);
        assert(p < k);
        exists(p, e);
    }
}

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
    /* code modified by LLM (iteration 5): implement hsplit using nested loops with invariants and proofs */
    let m: nat = arr@.len() / (k as nat);
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut p: usize = 0usize;
    while p < k
        invariant
            result@.len() == p as nat,
            forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == m,
        decreases k - p
    {
        let mut part: Vec<f32> = Vec::new();
        let mut e: usize = 0usize;
        while e < m as usize
            invariant
                part@.len() == e as nat,
                forall|j: int| 0 <= j < part@.len() ==> part@[j] == arr@[(p as int) * (m as int) + j],
            decreases (m as usize) - e
        {
            let old_e: usize = e;
            let v: f32 = arr[p * (m as usize) + e];
            part.push(v);
            proof {
                assert(part@.len() == old_e as nat + 1);
                assert(part@[old_e as int] == arr@[(p as int) * (m as int) + old_e as int]);
            }
            e = e + 1;
        }
        let old_p: usize = p;
        result.push(part);
        proof {
            assert(result@.len() == old_p as nat + 1);
            assert(result@[old_p as int].len() == m);
        }
        p = p + 1;
    }
    result
}

// </vc-code>


}
fn main() {}