use vstd::prelude::*;

verus! {

spec fn sum(v: Seq<int>) -> int {
    if v == seq![] { 
        0 
    } else if v.len() == 1 { 
        v[0] 
    } else { 
        v[0] + sum(v.subrange(1, v.len() as int)) 
    }
}

proof fn empty_lemma<T>(r: Seq<T>)
    requires multiset(r) == Multiset::empty(),
    ensures r == seq![],
{
}

proof fn elem_lemma<T>(s: Seq<T>, r: Seq<T>)
    requires 
        s != seq![] && multiset(s) == multiset(r),
    ensures 
        exists|i: int| 0 <= i < r.len() && r[i] == s[0] && 
        multiset(s.subrange(1, s.len() as int)) == 
        multiset(r.subrange(0, i).add(r.subrange(i + 1, r.len() as int))),
{
}

proof fn sum_elems_lemma(s: Seq<int>, r: Seq<int>)
    requires multiset(s) == multiset(r),
    ensures sum(s) == sum(r),
{
}

}