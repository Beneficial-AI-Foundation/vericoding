use vstd::prelude::*;

verus! {

spec fn sum(v: Seq<int>) -> int 
{
    if v =~= seq![] then 0
    else if v.len() == 1 then v[0]
    else v[0] + sum(v.subrange(1, v.len() as int))
}

proof fn empty_Lemma(r: Seq<int>)
    ensures r =~= seq![]
{
    if r !=~= seq![] {
    }
}

}