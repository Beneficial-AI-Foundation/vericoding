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
    let n = s.len();
    let ghost n_nat = n as nat;
    let v = Seq::new(2 * n_nat, |i: int|
        if i % 2 == 0 {
            x
        } else {
            s[i / 2]
        }
    );
    v
}
// </vc-code>

fn main() {}

}