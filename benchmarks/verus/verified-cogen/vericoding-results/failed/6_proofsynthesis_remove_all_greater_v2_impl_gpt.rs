// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
spec fn leq(x: i32, e: i32) -> bool { x <= e }
proof fn lemma_seq_contains_at_index(s: Seq<i32>, i: int)
    requires 0 <= i < s.len()
    ensures s.contains(s[i])
{ }
proof fn lemma_contains_of_push(s: Seq<i32>, a: i32)
    ensures s.push(a).contains(a)
{ }
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
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < res.len() ==> res[k] <= e && v@.contains(res[k]),
            forall |k:int| 0 <= k < i ==> v[k] <= e ==> res@.contains(v[k]),
        decreases v.len() - i
    {
        let x = v[i];
        i += 1;
        if x <= e {
            let ghost s = res@;
            res.push(x);
            proof {
                lemma_contains_of_push(s, x);
                assert(res@ == s.push(x));
                assert(res@.contains(x));
                assert(0 < i <= v.len());
                lemma_seq_contains_at_index(v@, (i - 1) as int);
            }
        }
    }
    res
}
// </vc-code>

}
fn main() {}