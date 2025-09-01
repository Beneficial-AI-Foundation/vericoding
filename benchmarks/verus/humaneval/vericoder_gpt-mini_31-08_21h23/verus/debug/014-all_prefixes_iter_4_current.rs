use vstd::prelude::*;

verus! {

// <vc-helpers>
pub proof fn seqs_equal_u8(a: Seq<u8>, b: Seq<u8>)
    requires a.len() == b.len(),
    requires forall|i: int| (0 <= i && i < a.len() ==> a@[i] == b@[i]),
    ensures a == b
{
    // From the pointwise equality and equal lengths, deduce sequence equality.
    assert(forall|i: int| 0 <= i && i < a.len() ==> a@[i] == b@[i]);
    assert(a == b);
}
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
    let n = s.len();
    let mut prefixes: Vec<Vec<u8>> = Vec::new();
    let mut i: nat = 0;

    while i < n
        invariant prefixes.len() == i,
        invariant forall|k: int| 0 <= k && k < i as int ==> prefixes[k as usize]@ == s@.subrange(0, k + 1)
    {
        let mut p: Vec<u8> = Vec::new();
        let mut j: nat = 0;
        while j <= i
            invariant p.len() == j,
            invariant forall|t: int| 0 <= t && t < j as int ==> p@[t] == s@[t]
        {
            p.push(s@[j as int]);
            j = j + 1;
        }

        proof {
            // After the inner loop, j == i + 1 and p has length i + 1 and matches s on [0, i]
            assert(j as int == i as int + 1);
            assert(p@.len() as int == (i as int + 1));
            assert(forall|t: int| 0 <= t && t < p@.len() ==> p@[t] == s@[t]);
            assert(p@.len() as int == s@.subrange(0, i as int + 1).len() as int);
            seqs_equal_u8(p@, s@.subrange(0, i as int + 1));
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