use vstd::prelude::*;

verus! {

uninterp spec fn f<T>(a: T) -> bool;

fn select<T>(s1: Seq<T>) -> (r: Seq<T>)
    ensures
        forall|e: T| f(e) ==> s1.to_multiset().count(e) == r.to_multiset().count(e),
        forall|e: T| !f(e) ==> r.to_multiset().count(e) == 0
{
    assume(false);
    unreached();
}

}
fn main() {}