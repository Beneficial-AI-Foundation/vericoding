use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_subrange_len<T>(s: Seq<T>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        s.subrange(0, i).len() == i as nat,
{
}

proof fn lemma_vec_ext_equal<T>(v1: Vec<T>, v2: Vec<T>)
    requires
        v1@ =~= v2@,
    ensures
        v1 == v2,
{
}

spec fn all_prefixes_spec(s: Seq<u8>, i: int) -> Seq<u8>
    recommends 0 <= i < s.len()
{
    s.subrange(0, i + 1)
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
    let mut prefixes = Vec::new();
    let mut current = Vec::new();
    let mut j: usize = 0;
    while j < s.len()
        invariant
            current@ == s@.subrange(0, j as int),
            prefixes.len() == j,
            forall|k: int| 0 <= k < j as int ==> prefixes@[k as usize]@ == s@.subrange(0, k + 1),
    {
        current.push(s[j]);
        let prefix_copy = current.clone();
        prefixes.push(prefix_copy);
        proof {
            lemma_seq_subrange_len(s@, (j + 1) as int);
        }
        j = j + 1;
    }
    prefixes
}
// </vc-code>

fn main() {}
}