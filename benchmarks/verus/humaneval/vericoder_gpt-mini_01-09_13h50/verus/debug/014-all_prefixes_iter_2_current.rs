use vstd::prelude::*;

verus! {

// <vc-helpers>
// Updated helpers: none needed for this proof.
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
        invariant(forall|k: int| #[trigger] 0 <= k && (k as usize) < i ==>
            prefixes[k as usize].len() == (k + 1) as usize &&
            (forall|m: int| 0 <= m && m <= k ==> prefixes[k as usize][m as usize] == s[m as usize])
        );
        let mut p: Vec<u8> = Vec::new();
        let mut j: usize = 0;
        while (j < i + 1) {
            invariant(j <= i + 1);
            invariant(p.len() == j);
            invariant(forall|m: int| #[trigger] 0 <= m && m < j as int ==> p[m as usize] == s[m as usize]);
            p.push(s[j]);
            j = j + 1;
        }
        // After inner loop, p has length i+1 and matches s[0..i]
        assert(p.len() == i + 1);
        assert(forall|m: int| 0 <= m && m < (i + 1) as int ==> p[m as usize] == s[m as usize]);
        prefixes.push(p);
        // Prove the invariant holds for the newly pushed prefix
        proof {
            // existing prefixes 0..i satisfy the invariant by the loop invariant;
            // need to show it for k = i
            assert(prefixes.len() == i + 1);
            assert(prefixes[i].len() == (i + 1) as usize);
            assert(forall|m: int| 0 <= m && m <= i as int ==> prefixes[i][m as usize] == s[m as usize]);
        }
        i = i + 1;
    }
    // final proofs to match the spec's int-indexed postcondition
    proof {
        assert(prefixes.len() == s.len());
        assert(forall|k: int| 0 <= k && (k as usize) < s.len() ==>
            prefixes[k as usize]@ == s@.subrange(0, k + 1));
    }
    prefixes
    // impl-end
}
// </vc-code>

fn main() {}
}