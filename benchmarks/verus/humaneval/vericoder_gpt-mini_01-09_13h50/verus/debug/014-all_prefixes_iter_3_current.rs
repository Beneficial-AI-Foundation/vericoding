use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemmas not required for this implementation.
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
    let mut i: usize = 0;
    while (i < s.len()) {
        invariant(i <= s.len());
        invariant(prefixes.len() == i);
        invariant(forall|k: usize| k < i ==>
            prefixes[k].len() == k + 1 &&
            (forall|m: usize| m <= k ==> prefixes[k][m] == s[m])
        );
        let mut p: Vec<u8> = Vec::new();
        let mut j: usize = 0;
        while (j < i + 1) {
            invariant(j <= i + 1);
            invariant(p.len() == j);
            invariant(forall|m: usize| m < j ==> p[m] == s[m]);
            p.push(s[j]);
            j = j + 1;
        }
        // After inner loop, p has length i+1 and matches s[0..i]
        assert(p.len() == i + 1);
        assert(forall|m: usize| m < (i + 1) ==> p[m] == s[m]);
        prefixes.push(p);
        // Prove the invariant holds for the newly pushed prefix
        proof {
            // existing prefixes 0..i satisfy the invariant by the loop invariant;
            // need to show it for k = i
            assert(prefixes.len() == i + 1);
            assert(prefixes[i].len() == (i + 1) as usize);
            assert(forall|m: usize| m <= i ==> prefixes[i][m] == s[m]);
        }
        i = i + 1;
    }
    // final proofs to match the spec's int-indexed postcondition
    proof {
        assert(prefixes.len() == s.len());
        // The loop invariant gives us element-wise facts for all k < prefixes.len()
        assert(forall|k: usize| k < prefixes.len() ==>
            prefixes[k].len() == k + 1 &&
            (forall|m: usize| m <= k ==> prefixes[k][m] == s[m])
        );
        // Convert the usize-indexed fact to the spec's int-indexed statement
        assert(forall|k: int|
            0 <= k && (k as usize) < prefixes.len() ==>
            {
                let ku: usize = k as usize;
                // lengths agree
                assert(prefixes[ku].len() == ku + 1);
                assert(prefixes[ku]@.len() == (ku + 1) as int);
                assert(s@.subrange(0, k + 1).len() == k + 1);
                // element-wise equality for indices 0..k
                assert(forall|m: int| 0 <= m && m < k + 1 ==>
                    prefixes[ku]@[m as usize] == s@[m as usize]);
                prefixes[ku]@ == s@.subrange(0, k + 1)
            }
        );
    }
    prefixes
    // impl-end
}
// </vc-code>

fn main() {}
}