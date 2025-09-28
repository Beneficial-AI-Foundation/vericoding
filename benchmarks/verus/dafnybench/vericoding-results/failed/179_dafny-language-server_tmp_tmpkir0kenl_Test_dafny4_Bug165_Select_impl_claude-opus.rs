use vstd::prelude::*;

verus! {

// Using generic type parameter with uninterpreted body
spec fn f<T>(a: T) -> bool {
    true  // placeholder uninterpreted function
}

// <vc-helpers>
// Helper lemma to prove multiset properties for the recursive construction
proof fn select_multiset_lemma<T>(s: Seq<T>, acc: Seq<T>, i: nat, elem: T)
    requires
        i <= s.len(),
        i > 0,
        elem == s[(i - 1) as int],
        forall|e: T| f(e) ==> s.subrange(0, (i - 1) as int).to_multiset().count(e) == 
            if f(elem) && acc.len() > 0 && acc[acc.len() - 1] == elem { 
                acc.subrange(0, (acc.len() - 1) as int).to_multiset().count(e) 
            } else { 
                acc.to_multiset().count(e) 
            },
        forall|e: T| !f(e) ==> acc.to_multiset().count(e) == 0,
    ensures
        forall|e: T| f(e) ==> s.subrange(0, i as int).to_multiset().count(e) == acc.to_multiset().count(e),
        forall|e: T| !f(e) ==> acc.to_multiset().count(e) == 0,
{
    assert forall|e: T| f(e) implies s.subrange(0, i as int).to_multiset().count(e) == acc.to_multiset().count(e) by {
        assert(s.subrange(0, i as int) =~= s.subrange(0, (i - 1) as int).push(elem));
        if e == elem {
            if f(elem) {
                assert(s.subrange(0, i as int).to_multiset().count(e) == 
                       s.subrange(0, (i - 1) as int).to_multiset().count(e) + 1);
                if acc.len() > 0 && acc[acc.len() - 1] == elem {
                    assert(acc.to_multiset().count(e) == 
                           acc.subrange(0, (acc.len() - 1) as int).to_multiset().count(e) + 1);
                }
            }
        }
    }
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
    let mut result: Seq<T> = seq![];
    let mut i: usize = 0;
    
    while i < s1.len()
        invariant
            i <= s1.len(),
            forall|e: T| f(e) ==> #[trigger] s1.subrange(0, i as int).to_multiset().count(e) == result.to_multiset().count(e),
            forall|e: T| !f(e) ==> #[trigger] result.to_multiset().count(e) == 0,
    {
        let old_result = result;
        let elem = s1[i as int];
        
        if f(elem) {
            result = result.push(elem);
        }
        
        proof {
            assert(s1.subrange(0, (i + 1) as int) =~= s1.subrange(0, i as int).push(elem));
            
            assert forall|e: T| f(e) implies s1.subrange(0, (i + 1) as int).to_multiset().count(e) == result.to_multiset().count(e) by {
                if e == elem {
                    if f(elem) {
                        assert(s1.subrange(0, (i + 1) as int).to_multiset().count(e) == 
                               s1.subrange(0, i as int).to_multiset().count(e) + 1);
                        assert(result.to_multiset().count(e) == 
                               old_result.to_multiset().count(e) + 1);
                    } else {
                        assert(result == old_result);
                    }
                } else {
                    assert(s1.subrange(0, (i + 1) as int).to_multiset().count(e) == 
                           s1.subrange(0, i as int).to_multiset().count(e));
                    assert(result.to_multiset().count(e) == old_result.to_multiset().count(e));
                }
            }
            
            assert forall|e: T| !f(e) implies result.to_multiset().count(e) == 0 by {
                if !f(e) {
                    if e == elem {
                        assert(result == old_result);
                    }
                    assert(old_result.to_multiset().count(e) == 0);
                }
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(s1.subrange(0, s1.len() as int) =~= s1);
    }
    
    result
}
// </vc-code>

fn main() {
}

}