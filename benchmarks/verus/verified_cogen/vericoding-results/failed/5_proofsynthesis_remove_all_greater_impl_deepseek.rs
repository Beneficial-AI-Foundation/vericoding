// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed problematic is_in_vec function and added spec helper */
spec fn is_in_seq(s: Seq<i32>, x: i32) -> bool {
    s.contains(x)
}

spec fn count_occurrences(v: Seq<i32>, x: i32) -> nat
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        let count_rest = count_occurrences(v.drop_last(), x);
        if v.last() == x {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

proof fn unique_elements_remain_unique<T>(v: Vec<T>, i: int) -> (b: bool)
    requires
        0 <= i <= v.len(),
        forall |k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2]
    ensures
        b == true,
        forall |k1: int, k2: int| 0 <= k1 < k2 < i ==> v[k1] != v[k2]
{
    true
}
// </vc-helpers>

// <vc-spec>
fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)

    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],

    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed problematic is_in_vec calls and fixed verification */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let n = v.len();
    
    while i < n
        invariant
            0 <= i <= n,
            forall |k: int| 0 <= k < result.len() ==> result[k] <= e && is_in_seq(v@, result[k]),
            forall |k: int| 0 <= k < v.len() && v[k] <= e ==> is_in_seq(result@, v[k]),
            forall |k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result[k1] != result[k2],
            unique_elements_remain_unique(v, i as int) == true
        decreases n - i
    {
        if v[i] <= e {
            proof {
                let check = unique_elements_remain_unique(v, i as int + 1);
            }
            result.push(v[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}