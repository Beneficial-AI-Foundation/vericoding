use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn CountEven(s: Seq<int>) -> int
    recommends positive(s)
{
    if s == seq![] {
        0
    } else {
        (if s[s.len() - 1] % 2 == 0 { 1 } else { 0 }) + CountEven(s.subrange(0, s.len() - 1))
    }
}

pub fn mcountEven(v: &[int]) -> (n: int)
    requires(positive(v@))
    ensures(n == CountEven(v@))
{
}

}