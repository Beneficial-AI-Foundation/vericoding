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
    let n: nat = s.len();
    let mut prefixes: Vec<Vec<u8>> = Vec::new();
    let mut i: nat = 0;
    while (i < n)
        invariant { i <= n }
        invariant { prefixes.len() == i }
        invariant { forall|k: nat| k < i ==> prefixes[k]@ == s@.subrange(0, k + 1) }
        decreases n - i
    {
        let mut p: Vec<u8> = Vec::new();
        let mut j: nat = 0;
        while (j < i + 1)
            invariant { j <= i + 1 }
            invariant { p.len() == j }
            invariant { forall|t: nat| t < j ==> p@[t] == s@[t] }
            decreases (i + 1) - j
        {
            p.push(s@[j]);
            j = j + 1;
        }
        proof {
            assert(p.len() == i + 1);
            assert(forall|t: nat| t < i + 1 ==> p@[t] == s@[t]);
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