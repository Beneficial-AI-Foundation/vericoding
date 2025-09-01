use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed.
// </vc-helpers>

// <vc-spec>
fn all_prefixes(s: &Vec<u8>) -> (prefixes: Vec<Vec<u8>>)
    // post-conditions-start
    ensures
        prefixes.len() == s.len(),
        forall|i: int| #![auto] 0 <= i < s.len() ==> prefixes[i]@ == s@.subrange(0, i + 1),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut prefixes: Vec<Vec<u8>> = Vec::new();
    let mut i: nat = 0;
    while (i < s.len()) {
        invariant(i <= s.len());
        invariant(prefixes.len() == i);
        invariant(forall|k: nat| #[trigger] k < i ==> prefixes[k]@ == s@.subrange(0, k + 1));
        let mut p: Vec<u8> = Vec::new();
        let mut j: nat = 0;
        while (j < i + 1) {
            invariant(j <= i + 1);
            invariant(p.len() == j);
            invariant(p@ == s@.subrange(0, j));
            p.push(s[j]);
            j = j + 1;
        }
        assert(p@ == s@.subrange(0, i + 1));
        prefixes.push(p);
        i = i + 1;
    }
    // final proofs to match the spec's int-indexed postcondition
    proof {
        assert(prefixes.len() == s.len());
        assert(forall|k: int| 0 <= k && k < s.len() ==>
            prefixes[k as nat]@ == s@.subrange(0, (k as nat) + 1));
        // The spec expects indexing by int; the above establishes the same fact.
    }
    prefixes
    // impl-end
}
// </vc-code>

fn main() {}
}