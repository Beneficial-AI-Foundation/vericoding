use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn find_first_repeated_char(s: &str) -> (result: (bool, char))
    ensures 
        (result.0 ==> exists|i: int, j: int| 0 <= i < j < s@.len() && s@[i] == s@[j] && s@[i] == result.1 && 
            (forall|k: int, l: int| 0 <= k < l < j && s@[k] == s@[l] ==> k >= i)) &&
        (!result.0 ==> (forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] != s@[j]))
// </vc-spec>
// <vc-code>
{
    let seq: Seq<char> = s@;
    let n: int = seq.len();

    let mut j: int = 0;
    while j < n
        invariant 0 <= j && j <= n
        invariant forall |k: int, l: int| 0 <= k && k < l && l < j ==> #[trigger] (seq@[k] != seq@[l])
        decreases n - j
    {
        let mut i: int = 0;
        while i < j
            invariant 0 <= i && i <= j
            invariant forall |k: int| 0 <= k && k < i ==> #[trigger] (seq@[k] != seq@[j])
            decreases j - i
        {
            if seq@[i] == seq@[j] {
                proof {
                    assert(0 <= i && i < j && j < n);
                    assert(seq@[i] == seq@[j]);
                    // prefix [0, j) has no duplicates, so the implication in the postcondition holds vacuously
                    assert(forall |k: int, l: int| 0 <= k && k < l && l < j ==> #[trigger] (seq@[k] != seq@[l]));
                    assert(forall |k: int, l: int| 0 <= k && k < l && l < j ==> #[trigger] (seq@[k] == seq@[l] ==> k >= i));
                }
                return (true, seq@[i]);
            }
            i = i + 1;
        }
        proof {
            // from invariants: no duplicates in [0, j) and no k<j with seq[k]==seq[j], hence no duplicates in [0, j+1)
            assert(forall |k: int, l: int| 0 <= k && k < l && l < j ==> #[trigger] (seq@[k] != seq@[l]));
            assert(forall |k: int| 0 <= k && k < j ==> #[trigger] (seq@[k] != seq@[j]));
            assert(forall |k: int, l: int| 0 <= k && k < l && l < j+1 ==> #[trigger] (seq@[k] != seq@[l]));
        }
        j = j + 1;
    }
    proof {
        assert(forall |k: int, l: int| 0 <= k && k < l && l < n ==> #[trigger] (seq@[k] != seq@[l]));
    }
    (false, 'a')
}
// </vc-code>

fn main() {}

}