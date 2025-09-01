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
proof fn counter_implies_unhappy(seq: Seq<char>, idx: int)
    requires 0 < idx && idx + 1 < seq.len()
    requires !(three_distinct_spec(seq, idx))
{
    // From the counterexample we get that the universal property does not hold.
    assert(!(forall|t: int| 0 < t && t + 1 < seq.len() ==> three_distinct_spec(seq, t)));
    // Therefore the conjunction in happy_spec is false, so happy_spec(seq) is false.
    assert(!(seq.len() >= 3 && (forall|t: int| 0 < t && t + 1 < seq.len() ==> three_distinct_spec(seq, t))));
}
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
        invariant (forall|j: int| 0 < j && j + 1 < seq.len() && j < (i as int) ==> #[trigger] three_distinct_spec(seq, j))
        decreases seq.len() - i
    {
        let idx: int = i as int;
        let a = seq@[idx - 1];
        let b = seq@[idx];
        let c = seq@[idx + 1];
        if !(a != b && b != c) {
            proof {
                assert(0 < idx && idx + 1 < seq.len());
                assert(!(three_distinct_spec(seq, idx)));
                counter_implies_unhappy(seq, idx);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        // At loop exit, i + 1 >= seq.len() and invariant gives i + 1 <= seq.len(),
        // hence i + 1 == seq.len().
        assert(i + 1 == seq.len());
        // From the invariant we have the property for all int indices k < i
        assert(forall|k: int| 0 < k && k + 1 < seq.len() ==>
            {
                assert(k + 1 < (i as int) + 1);
                assert(k < i as int);
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