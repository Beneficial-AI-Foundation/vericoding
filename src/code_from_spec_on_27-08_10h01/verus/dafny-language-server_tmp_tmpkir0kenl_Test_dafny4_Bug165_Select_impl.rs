use vstd::prelude::*;

verus! {

// Using generic type parameter with uninterpreted body
spec fn f<T>(a: T) -> bool {
    true  // placeholder uninterpreted function
}

// <vc-helpers>
spec fn seq_filter<T>(s: Seq<T>) -> Seq<T>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let rest = seq_filter(s.subrange(1, s.len() as int));
        if f(s[0]) {
            seq![s[0]] + rest
        } else {
            rest
        }
    }
}

proof fn seq_filter_preserves_count<T>(s: Seq<T>, e: T)
    ensures
        f(e) ==> s.to_multiset().count(e) == seq_filter(s).to_multiset().count(e),
        !f(e) ==> seq_filter(s).to_multiset().count(e) == 0,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        seq_filter_preserves_count(s.subrange(1, s.len() as int), e);
        if f(s[0]) {
            assert(seq_filter(s) =~= seq![s[0]] + seq_filter(s.subrange(1, s.len() as int)));
        } else {
            assert(seq_filter(s) =~= seq_filter(s.subrange(1, s.len() as int)));
        }
    }
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
#[verifier::exec_allows_no_decreases_clause]
fn select<T>(s1: Seq<T>) -> (r: Seq<T>)
    ensures
        forall|e: T| f(e) ==> s1.to_multiset().count(e) == r.to_multiset().count(e),
        forall|e: T| !f(e) ==> r.to_multiset().count(e) == 0,
{
    proof {
        assert forall|e: T| f(e) ==> s1.to_multiset().count(e) == seq_filter(s1).to_multiset().count(e) by {
            seq_filter_preserves_count(s1, e);
        };
        assert forall|e: T| !f(e) ==> seq_filter(s1).to_multiset().count(e) == 0 by {
            seq_filter_preserves_count(s1, e);
        };
    }
    seq_filter(s1)
}
// </vc-code>

fn main() {
}

}