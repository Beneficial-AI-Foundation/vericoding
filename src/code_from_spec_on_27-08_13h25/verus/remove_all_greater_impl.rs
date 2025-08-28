use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn vec_contains_implies_exists(v: Seq<i32>, val: i32)
    requires
        v.contains(val),
    ensures
        exists |i: int| 0 <= i < v.len() && v[i] == val,
{
    let mut i: int = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |j: int| 0 <= j < i ==> v[j] != val,
    {
        if v[i] == val {
            return;
        }
        i = i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    // pre-conditions-start
    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires
        forall |k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
    ensures
        forall |k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i = i + 1;
    }

    result
}
// </vc-code>

}

fn main() {}