use vstd::prelude::*;

verus! {

// Using generic type parameter with uninterpreted body
spec fn f<T>(a: T) -> bool {
    true  // placeholder uninterpreted function
}

// <vc-helpers>
#[verifier::exec_external]
fn is_true<T>(a: T) -> bool {
    f(a)
}
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn select<T>(s1: Seq<T>) -> (r: Seq<T>)
    ensures
        forall|e: T| f(e) ==> s1.to_multiset().count(e) == r.to_multiset().count(e),
        forall|e: T| !f(e) ==> r.to_multiset().count(e) == 0,

fn main_impl<T>(s1: Seq<T>)
// </vc-spec>
// <vc-code>
{
    let mut vec_r: Vec<T> = Vec::new();
    let mut i = 0;
    while i < s1.len()
        invariant
            0 <= i && i <= s1.len(),
            vec_r.len() as nat <= s1.len(),
            forall|e: T| (#[trigger] f(e)) ==> (s1.subsequence(0, i).to_multiset().count(e) == vec_r.to_seq().to_multiset().count(e) + s1.subsequence(0, i).filter(|elem: T| !f(elem)).to_multiset().count(e)),
            forall|e: T| (#[trigger] !f(e)) ==> (vec_r.to_seq().to_multiset().count(e) == 0),
    {
        let elem = s1.index(i);
        if is_true(elem) {
            vec_r.push(elem);
            proof {
                assert(vec_r.to_seq().to_multiset().count(elem) == old(vec_r.to_seq()).to_multiset().count(elem) + 1);
            }
        }
        i = i + 1;
    }
    vec_r.to_seq()
}
// </vc-code>

fn main() {
}

}