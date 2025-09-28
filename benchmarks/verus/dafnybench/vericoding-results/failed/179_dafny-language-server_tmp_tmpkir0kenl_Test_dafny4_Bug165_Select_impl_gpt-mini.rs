use vstd::prelude::*;

verus! {

// Using generic type parameter with uninterpreted body
spec fn f<T>(a: T) -> bool {
    true  // placeholder uninterpreted function
}

// <vc-helpers>
// Updated helper proofs (none needed for this verification)
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
    // Implementation for `select<T>(s1: Seq<T>) -> (r: Seq<T>)`
    let mut rvec: Vec<T> = Vec::new();
    let mut i: nat = 0;
    proof {
        // loop invariants to be established via the while loop below
    }
    while i < s1.len()
        invariant i <= s1.len()
        invariant forall|x: T| f(x) ==> rvec.view().to_multiset().count(x) == s1.slice(0, i).to_multiset().count(x)
        invariant forall|x: T| !f(x) ==> rvec.view().to_multiset().count(x) == 0
    {
        let e = s1@[i];
        if f(e) {
            rvec.push(e);
            proof {
                // After pushing e, update counts for all x
                assert(forall|x: T| f(x) ==> rvec.view().to_multiset().count(x) == s1.slice(0, i + 1).to_multiset().count(x));
                assert(forall|x: T| !f(x) ==> rvec.view().to_multiset().count(x) == 0);
            }
        } else {
            proof {
                // No change to rvec, but slice grows
                assert(forall|x: T| f(x) ==> rvec.view().to_multiset().count(x) == s1.slice(0, i + 1).to_multiset().count(x));
                assert(forall|x: T| !f(x) ==> rvec.view().to_multiset().count(x) == 0);
            }
        }
        i = i + 1;
    }
    let r = rvec.view();
    proof {
        // Postconditions follow from the loop invariants at termination (i == s1.len())
        assert(i == s1.len());
        assert(forall|x: T| f(x) ==> r.to_multiset().count(x) == s1.to_multiset().count(x));
        assert(forall|x: T| !f(x) ==> r.to_multiset().count(x) == 0);
    }
    r
}
{
    // Implementation for `main_impl<T>(s1: Seq<T>)`
    let _ = select(s1);
}
// </vc-code>

fn main() {
}

}