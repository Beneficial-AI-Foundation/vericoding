use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn any_value_exists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures result <==> (exists|i: int| 0 <= i < seq1.len() && seq2.contains(seq1[i]))
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    let mut res: bool = false;
    while i < seq1.len()
        invariant 0 <= i <= seq1.len()
        invariant res <==> (exists|j:int, t:int| 0 <= j < i && 0 <= t < seq2.len() && #[trigger] seq2[t] == seq1[j])
    {
        let a = seq1[i];
        let mut k: int = 0;
        let mut found_i: bool = false;
        while k < seq2.len()
            invariant 0 <= k <= seq2.len()
            invariant found_i <==> (exists|t:int| 0 <= t < k && #[trigger] seq2[t] == a)
        {
            if seq2[k] == a {
                found_i = true;
            }
            k = k + 1;
        }
        proof {
            assert(k == seq2.len());
            assert(found_i ==> (exists|t:int| 0 <= t < k && #[trigger] seq2[t] == a));
            assert(!found_i ==> !(exists|t:int| 0 <= t < k && #[trigger] seq2[t] == a));
            assert(found_i <==> (exists|t:int| 0 <= t < seq2.len() && #[trigger] seq2[t] == a));
            assert(found_i <==> (exists|t:int| 0 <= t < seq2.len() && #[trigger] seq2[t] == seq1[i]));
            // Combine the previous invariant with found_i to get the next-step characterization
            assert(
                (res || found_i)
                <==>
                (exists|j:int, t:int|
                    0 <= j < i + 1 && 0 <= t < seq2.len() && #[trigger] seq2[t] == seq1[j]
                )
            );
        }
        res = res || found_i;
        i = i + 1;
    }
    proof {
        assert(i == seq1.len());
        assert(forall|x:int| seq2.contains(x) <==> (exists|t:int| 0 <= t < seq2.len() && #[trigger] seq2[t] == x));
    }
    res
}
// </vc-code>

fn main() {}

}