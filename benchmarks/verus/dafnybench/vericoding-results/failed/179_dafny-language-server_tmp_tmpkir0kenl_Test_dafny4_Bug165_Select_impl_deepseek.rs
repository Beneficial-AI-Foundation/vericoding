use vstd::prelude::*;

verus! {

// Using generic type parameter with uninterpreted body
spec fn f<T>(a: T) -> bool {
    true  // placeholder uninterpreted function
}

// <vc-helpers>
spec fn f<T>(a: T) -> bool;

proof fn filter_preserves_count<T>(s: Seq<T>, e: T) 
    ensures
        f(e) ==> s.filter(|x: T| f(x)).count(e) == s.count(e),
        !f(e) ==> s.filter(|x: T| f(x)).count(e) == 0,
{
    reveal_with_fuel(f, 2);
    s.filter_lemma(|x: T| f(x));
}

proof fn filter_preserves_count_multiset<T>(s: Seq<T>, e: T)
    ensures
        f(e) ==> s.filter(|x: T| f(x)).to_multiset().count(e) == s.to_multiset().count(e),
        !f(e) ==> s.filter(|x: T| f(x)).to_multiset().count(e) == 0,
{
    filter_preserves_count(s, e);
    assert(s.filter(|x: T| f(x)).count(e) == s.filter(|x: T| f(x)).to_multiset().count(e));
    assert(s.count(e) == s.to_multiset().count(e));
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
    let mut result: Seq<T> = Seq::empty();
    let mut i: int = 0;
    while i < s1.len() 
        invariant
            0 <= i <= s1.len(),
            forall|e: T| f(e) ==> result.to_multiset().count(e) == s1.subrange(0, i).filter(|x: T| f(x)).to_multiset().count(e),
            forall|e: T| !f(e) ==> result.to_multiset().count(e) == 0,
    {
        let elem = s1[i];
        if f(elem) {
            result = result.push(elem);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}