use vstd::prelude::*;

verus! {

// Using generic type parameter with uninterpreted body
spec fn f<T>(a: T) -> bool {
    true  // placeholder uninterpreted function
}

// <vc-helpers>

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
    s1
},
{
    let _r = select::<T>(s1);
}
// </vc-code>

fn main() {
}

}