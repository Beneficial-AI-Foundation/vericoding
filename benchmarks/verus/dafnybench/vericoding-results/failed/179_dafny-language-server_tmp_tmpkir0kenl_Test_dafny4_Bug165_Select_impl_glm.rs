use vstd::prelude::*;

verus! {

// Using generic type parameter with uninterpreted body
spec fn f<T>(a: T) -> bool {
    true  // placeholder uninterpreted function
}

// <vc-helpers>
proof fn multiset_filter<T>(s: Seq<T>) -> (res: Multiset<T>)
    ensures
        forall|e: T| res.count(e) == if f(e) { s.to_multiset().count(e) } else { 0 },
    decreases s.len(),
{
    if s.len() == 0 {
        Multiset::empty()
    } else {
        let tail = s.subrange(1, s.len() as int);
        let m_tail = multiset_filter(tail);
        if f(s[0]) {
            let res = m_tail.insert(s[0]);
            proof {
                assert forall|e: T|
                    res.count(e) == if f(e) { s.to_multiset().count(e) } else { 0 }
                by {
                    if e == s[0] {
                        assert(m_tail.count(e) == tail.to_multiset().count(e));
                        assert(res.count(e) == m_tail.count(e) + 1);
                        assert(s.to_multiset().count(e) == tail.to_multiset().count(e) + 1);
                    } else {
                        assert(m_tail.count(e) == if f(e) { tail.to_multiset().count(e) } else { 0 });
                        assert(s.to_multiset().count(e) == tail.to_multiset().count(e));
                    }
                }
            }
            res
        } else {
            proof {
                assert forall|e: T|
                    m_tail.count(e) == if f(e) { s.to_multiset().count(e) } else { 0 }
                by {
                    if e == s[
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
proof fn multiset_filter<T>(s: Seq<T>) -> (res: Multiset<T>)
    ensures
        forall|e: T| res.count(e) == if f(e) { s.to_multiset().count(e) } else { 0 },
    decreases s.len(),
{
    if s.len() == 0 {
        Multiset::empty()
    } else {
        let tail = s.subrange(1, s.len() as int);
        let m_tail = multiset_filter(tail);
        if f(s[0]) {
            let res = m_tail.insert(s[0]);
            proof {
                assert forall|e: T|
                    res.count(e) == if f(e) { s.to_multiset().count(e) } else { 0 }
                by {
                    if e == s[0] {
                        assert(m_tail.count(e) == tail.to_multiset().count(e));
                        assert(res.count(e) == m_tail.count(e) + 1);
                        assert(s.to_multiset().count(e) == tail.to_multiset().count(e) + 1);
                    } else {
                        assert(m_tail.count(e) == if f(e) { tail.to_multiset().count(e) } else { 0 });
                        assert(s.to_multiset().count(e) == tail.to_multiset().count(e));
                    }
                }
            }
            res
        } else {
            proof {
                assert forall|e: T|
                    m_tail.count(e) == if f(e) { s.to_multiset().count(e) } else { 0 }
                by {
                    if e == s[
// </vc-code>

fn main() {
}

}