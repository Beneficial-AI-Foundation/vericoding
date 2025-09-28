use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
// No helper lemmas needed for this solution.
// </vc-helpers>

// <vc-spec>
fn mfirstNegative(v: &[int]) -> (result: (bool, usize))
    ensures 
        (result.0 <==> exists|k: int| 0 <= k < v.len() && v[k] < 0) &&
        (result.0 ==> (result.1 < v.len() && v[result.1 as int] < 0 && positive(v@.subrange(0, result.1 as int))))
// </vc-spec>
// <vc-code>
{
    let s = v@;
    let mut i: usize = 0;
    let mut found: bool = false;
    let mut idx: usize = 0;
    while i < v.len() && !found
        invariant { i <= v.len(); }
        invariant { 0 <= i as int && i as int <= s.len(); }
        invariant { forall|u: int| 0 <= u && u < i as int ==> s[u] >= 0; }
    {
        if v[i] < 0 {
            found = true;
            idx = i;
        } else {
            i = i + 1;
        }
    }
    if found {
        // idx was set when the first negative was found; i did not advance past it
        assert(idx < v.len());
        assert(s[idx as int] < 0);
        // prefix up to idx is non-negative by the loop invariant (with i == idx at the time of setting)
        assert(forall|u: int| 0 <= u && u < idx as int ==> s[u] >= 0);
        // this implies positivity of the subrange [0, idx)
        assert(positive(s.subrange(0, idx as int)));
        (true, idx)
    } else {
        // loop exited without finding a negative: i == v.len()
        assert(i == v.len());
        // prefix invariant now covers the whole sequence
        assert(forall|u: int| 0 <= u && u < s.len() ==> s[u] >= 0);
        // therefore there is no negative element
        assert(!(exists|k: int| 0 <= k && k < s.len() && s[k] < 0));
        (false, 0)
    }
}
// </vc-code>

fn main() {
}

}