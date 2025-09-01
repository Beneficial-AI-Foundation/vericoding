use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n = s.len();
    let mut prefixes = Vec::new();
    for i in 0..n {
        invariant(i <= n);
        invariant(prefixes.len() == i);
        invariant(forall j: int :: (0 <= j && j < i) ==> #[trigger] (prefixes[j]@ == s@.subrange(0, j+1)));
        let prefix = Vec::from(&s@.subrange(0, i+1));
        prefixes.push(prefix);
    }
    prefixes
}
// </vc-code>

fn main() {}
}