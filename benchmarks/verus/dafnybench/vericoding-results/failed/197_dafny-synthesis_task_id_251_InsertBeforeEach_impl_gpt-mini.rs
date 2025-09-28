use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    proof {
        let mut res: Seq<String> = Seq::empty();
        let mut i: int = 0;
        while i < s.len()
            invariant 0 <= i && i <= s.len(),
            invariant res.len() == 2 * i,
            invariant forall|j: int| 0 <= j && j < i ==> res[2*j] == x && res[2*j + 1] == s[j]
        {
            res = res + seq![x.clone()] + seq![s[i].clone()];
            i = i + 1;
        }
        return res;
    }
}
// </vc-code>

fn main() {}

}