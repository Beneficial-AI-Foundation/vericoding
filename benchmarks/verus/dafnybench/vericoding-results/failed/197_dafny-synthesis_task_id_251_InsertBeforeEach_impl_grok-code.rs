use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut result = Seq::empty();
    for i in 0..s.len() {
        result = result.push(x);
        result = result.push(s[i]);
    }
    result
}
// </vc-code>

fn main() {}

}