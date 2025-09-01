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
    let mut i: nat = 0;
    while i < n {
        // loop invariant: i <= n && prefixes.len() == i && forall |j: int| #![auto] 0 <= j < i ==> prefixes[j]@ == s@.subrange(0, j+1)
        let cur_prefix = s@.subrange(0, i+1).to_vec();
        prefixes.push(cur_prefix);
        i += 1;
    }
    prefixes
}
// </vc-code>

fn main() {}
}