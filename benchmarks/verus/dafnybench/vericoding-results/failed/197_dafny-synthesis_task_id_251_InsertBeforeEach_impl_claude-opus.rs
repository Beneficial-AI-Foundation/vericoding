use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn insert_before_each(s: Seq<String>, x: String) -> (v: Seq<String>)
    ensures
        v.len() == 2 * s.len(),
        forall|i: int| 0 <= i < s.len() ==> v[2*i] == x && v[2*i + 1] == s[i],
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<String> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            v@.len() == 2 * i as int,
            forall|j: int| 0 <= j < i as int ==> v@[2*j] == x && v@[2*j + 1] == s[j],
    {
        v.push(x.clone());
        v.push(s[i].clone());
        i = i + 1;
    }
    
    v@
}
// </vc-code>

fn main() {}

}