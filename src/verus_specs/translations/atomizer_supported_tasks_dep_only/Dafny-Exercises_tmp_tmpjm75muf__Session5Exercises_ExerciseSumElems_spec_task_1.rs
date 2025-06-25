use vstd::prelude::*;

verus! {

// ATOM 
spec fn SumR(s: Seq<int>) -> int
{
    if s == seq![] { 0 }
    else { SumR(s.subrange(0, s.len() as int - 1)) + s[s.len() - 1] }
}

// ATOM 
spec fn SumL(s: Seq<int>) -> int
{
    if s == seq![] { 0 }
    else { s[0] + SumL(s.subrange(1, s.len() as int)) }
}

//ATOM_PLACEHOLDER_concatLast
//ATOM_PLACEHOLDER_concatFirst

//ATOM_PLACEHOLDER_unknown_369 
proof fn SumByPartsR(s: Seq<int>, t: Seq<int>)
    ensures SumR(s + t) == SumR(s) + SumR(t)
{
}

//ATOM_PLACEHOLDER_unknown_875 
proof fn SumByPartsL(s: Seq<int>, t: Seq<int>)
    ensures SumL(s + t) == SumL(s) + SumL(t)
{
}

//ATOM_PLACEHOLDER_unknown_1289 
proof fn equalSumR(s: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= s.len()
    ensures SumR(s.subrange(i, j)) == SumL(s.subrange(i, j))
{
}

//ATOM_PLACEHOLDER_equalSumsV

// ATOM 
spec fn SumV(v: &[int], c: int, f: int) -> int
    recommends 0 <= c <= f <= v.len()
{
    SumR(v@.subrange(c, f))
}

//ATOM_PLACEHOLDER_ArrayFacts

// SPEC 
pub fn sumElems(v: &[int]) -> (sum: int)
    ensures sum == SumR(v@)
{
}

}