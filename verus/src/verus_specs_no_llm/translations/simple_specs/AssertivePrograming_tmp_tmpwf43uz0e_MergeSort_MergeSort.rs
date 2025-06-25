// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall i,j :: 0 <= i <= j < q.len() ==> q.spec_index(i) <= q.spec_index(j)
}

fn Merge(b: Vec<int>, c: Vec<int>, d: Vec<int>) -> (b: Vec<int>)
    requires
        b != c && b != d && b.len() == c.len() + d.len(),
        Sorted(c.spec_index(..)) && Sorted(d.spec_index(..))
    ensures
        Sorted(b.spec_index(..)) && multiset(b.spec_index(..)) == multiset(c.spec_index(..))+multiset(d.spec_index(..))
	modifies b,
        b.len() == a.len() && Sorted(b.spec_index(..)) && multiset(a.spec_index(..)) == multiset(b.spec_index(..))
{
    return Vec::new();
}

}