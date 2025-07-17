// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < q.len() ==> q.index(i) <= q.index(j)
}

spec fn spec_Merge(b: Vec<int>, c: Vec<int>, d: Vec<int>) -> b: array<int>
    requires
        b != c && b != d && b.len() == c.len() + d.len(),
        Sorted(c.index(..)) && Sorted(d.index(..))
    ensures
        Sorted(b.index(..)) && multiset(b.index(..)) == multiset(c.index(..))+multiset(d.index(..))
	modifies b,
        b.len() == a.len() && Sorted(b.index(..)) && multiset(a.index(..)) == multiset(b.index(..))
;

proof fn lemma_Merge(b: Vec<int>, c: Vec<int>, d: Vec<int>) -> (b: Vec<int>)
    requires
        b != c && b != d && b.len() == c.len() + d.len(),
        Sorted(c.index(..)) && Sorted(d.index(..))
    ensures
        Sorted(b.index(..)) && multiset(b.index(..)) == multiset(c.index(..))+multiset(d.index(..))
	modifies b,
        b.len() == a.len() && Sorted(b.index(..)) && multiset(a.index(..)) == multiset(b.index(..))
{
    Vec::new()
}

}