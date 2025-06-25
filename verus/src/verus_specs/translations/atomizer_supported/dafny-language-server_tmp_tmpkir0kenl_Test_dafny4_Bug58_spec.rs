use vstd::prelude::*;

verus! {

spec fn M1(f: Map<int, bool>, i: int) -> bool

spec fn M2(f: Map<int, bool>, i: int) -> bool
{
    M1(Map::new(|j: int| f.dom().contains(j), |j: int| f[j]), i)
}

proof fn L(f: Map<int, bool>, i: int)
    requires(f.dom().contains(i))
    requires(M2(f, i))
    requires(forall |j: int, f: Map<int, bool>| M1(f, j) == (f.dom().contains(j) && f[j]))
{
}

}