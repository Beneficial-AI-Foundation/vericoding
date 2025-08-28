use vstd::prelude::*;

verus! {

// Using generic type parameter with uninterpreted body
spec fn f<T>(a: T) -> bool {
    true  // placeholder uninterpreted function
}

// <vc-helpers>
proof fn lemma_multiset_count_preservation<T>(s1: Seq<T>, r: Seq<T>, e: T)
    requires
        forall|i: int| 0 <= i < s1.len() ==> (f(s1@[i]) ==> r.to_multiset().count(s1@[i]) == s1.to_multiset().count(s1@[i])),
        forall|i: int| 0 <= i < s1.len() ==> (!f(s1@[i]) ==> r.to_multiset().count(s1@[i]) == 0),
    ensures
        f(e) ==> r.to_multiset().count(e) == s1.to_multiset().count(e),
        !f(e) ==> r.to_multiset().count(e) == 0,
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn select<T>(s1: Seq<T>) -> (r: Seq<T>)
    ensures
        forall|e: T| f(e) ==> s1.to_multiset().count(e) == r.to_multiset().count(e),
        forall|e: T| !f(e) ==> r.to_multiset().count(e) == 0,

fn main_impl<T>(s1: Seq<T>)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn select<T>(s1: Seq<T>) -> (r: Seq<T>)
    ensures
        forall|e: T| f(e) ==> s1.to_multiset().count(e) == r.to_multiset().count(e),
        forall|e: T| !f(e) ==> r.to_multiset().count(e) == 0,
{
    let mut result: Vec<T> = Vec::new();
    let mut i: usize = 0;
    
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            forall|j: int| 0 <= j < i ==> (f(s1@[j]) ==> result.to_seq().to_multiset().count(s1@[j]) == 1),
            forall|j: int| 0 <= j < i ==> (!f(s1@[j]) ==> result.to_seq().to_multiset().count(s1@[j]) == 0),
            result.len() <= i,
    {
        if f(s1@[i]) {
            result.push(s1@[i]);
        }
        i = i + 1;
    }
    
    result.to_seq()
}

fn main_impl<T>(s1: Seq<T>) -> (result: Seq<T>)
    ensures
        result == select(s1),
{
    let result = select(s1);
    result
}
// </vc-code>

fn main() {
}

}