use vstd::prelude::*;

verus! {

// Using generic type parameter with uninterpreted body
spec fn f<T>(a: T) -> bool {
    true  // placeholder uninterpreted function
}

// <vc-helpers>
// Helper lemmas for multiset properties if needed
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
    // Implementation of select function that filters elements based on predicate f
    let mut result: Vec<T> = Vec::new();
    let mut i = 0;
    
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            forall|e: T| f(e) ==> s1.subrange(0, i as int).to_multiset().count(e) == result@.to_multiset().count(e),
            forall|e: T| !f(e) ==> result@.to_multiset().count(e) == 0,
    {
        if f(s1[i]) {
            result.push(s1[i]);
        }
        i += 1;
    }
    
    result@
}
// </vc-code>

fn main() {
}

}