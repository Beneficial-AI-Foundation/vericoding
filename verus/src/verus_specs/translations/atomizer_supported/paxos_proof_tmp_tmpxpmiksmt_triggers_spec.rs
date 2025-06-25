use vstd::prelude::*;

verus! {

spec fn P(x: int) -> bool;

spec fn Q(x: int) -> bool;

proof fn M(a: Seq<int>, m: Map<bool, int>)
    requires
        2 <= a.len(),
        m.contains_key(false) && m.contains_key(true),
{
    assume(forall|i: int| 0 <= i < a.len()-1 ==> a[i] <= a[i+1]);
    let x: int;
    assume(0 <= x <= a.len()-2);
}

}