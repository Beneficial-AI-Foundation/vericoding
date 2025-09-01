use vstd::prelude::*;

verus! {

spec fn three_distinct_spec(s: Seq<char>, i: int) -> (ret:bool)
    recommends
        0 < i && i + 1 < s.len(),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i] != s[i + 1])
}
// pure-end
spec fn happy_spec(s: Seq<char>) -> (ret:bool) {
    s.len() >= 3 && (forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec(s, i))
}
// pure-end

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_happy(s: &Vec<char>) -> (happy: bool)
    // post-conditions-start
    ensures
        happy <==> happy_spec(s@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let seq: Seq<char> = s@;
    if seq.len() < 3 {
        return false;
    }
    let mut i: nat = 1;
    while i + 1 < seq.len()
        invariant 0 < i && i + 1 <= seq.len()
        invariant forall|j: nat| 0 < j && j + 1 < seq.len() && j < i ==> three_distinct_spec(seq, j as int)
        decreases seq.len() - i
    {
        let idx: int = i as int;
        let a = seq@[idx - 1];
        let b = seq@[idx];
        let c = seq@[idx + 1];
        if !(a != b && b != c) {
            proof {
                // witness idx is a counterexample to the "forall" in happy_spec
                assert(0 < idx && idx + 1 < seq.len());
                assert(!(three_distinct_spec(seq, idx)));
                // therefore the universal property fails, so happy_spec(seq) is false
                assert(!(forall|t: int| 0 < t && t + 1 < seq.len() ==> three_distinct_spec(seq, t)));
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        // At loop exit, !(i + 1 < seq.len()) holds, and invariant gives i + 1 <= seq.len(),
        // hence i + 1 == seq.len().
        assert(i + 1 == seq.len());
        // From the invariant we have the property for all j < i; show it for all int indices k
        assert(forall|k: int| 0 < k && k + 1 < seq.len() ==>
            {
                let j: nat = (k as nat);
                // k >= 1 ensures cast is valid and j+1 < seq.len()
                assert(j + 1 < seq.len());
                // since i + 1 == seq.len(), j + 1 < seq.len() implies j + 1 < i + 1, hence j < i
                assert(j + 1 < i + 1);
                assert(j < i);
                // use loop invariant
                assert(three_distinct_spec(seq, k));
                true
            }
        );
    }
    true
}
// </vc-code>

fn main() {}
}