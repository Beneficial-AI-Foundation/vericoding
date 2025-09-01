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
    let n: int = s.len() as int;
    let mut prefixes: Vec<Vec<u8>> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n,
        invariant (prefixes.len() as int) == i,
        invariant forall|k: int| 0 <= k < i ==> prefixes[k]@ == s@.subrange(0, k + 1),
        decreases n - i
    {
        let mut p: Vec<u8> = Vec::new();
        let mut j: int = 0;
        while j <= i
            invariant 0 <= j && j <= i + 1,
            invariant (p.len() as int) == j,
            invariant forall|t: int| 0 <= t < j ==> p@[t] == s@[t],
            decreases (i + 1) - j
        {
            p.push(s@[j]);
            j = j + 1;
        }
        proof {
            assert((p.len() as int) == i + 1);
            assert(forall|t: int| 0 <= t < i + 1 ==> p@[t] == s@[t]);
            assert(p@ == s@.subrange(0, i + 1));
        }
        prefixes.push(p);
        i = i + 1;
    }
    prefixes
    // impl-end
}
// </vc-code>

fn main() {}
}