// ATOM 
spec fn SumR(s: Seq<int>) -> int
{
    if s.len() == 0 { 0 } else { SumR(s.subrange(0, s.len() - 1)) + s[s.len() - 1] }
}

// ATOM 
spec fn SumL(s: Seq<int>) -> int
{
    if s.len() == 0 { 0 } else { s[0] + SumL(s.subrange(1, s.len())) }
}

// ATOM 
proof fn concatLast(s: Seq<int>, t: Seq<int>)
    requires t.len() != 0
    ensures (s + t).subrange(0, (s + t).len() - 1) == s + t.subrange(0, t.len() - 1)
{
}

// ATOM 
proof fn concatFirst(s: Seq<int>, t: Seq<int>)
    requires s.len() != 0
    ensures (s + t).subrange(1, (s + t).len()) == s.subrange(1, s.len()) + t
{
}

proof fn SumByPartsR(s: Seq<int>, t: Seq<int>)
    ensures SumR(s + t) == SumR(s) + SumR(t)
{
}

proof fn SumByPartsL(s: Seq<int>, t: Seq<int>)
    ensures SumL(s + t) == SumL(s) + SumL(t)
{
}

proof fn equalSumR(s: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= s.len()
    ensures SumR(s.subrange(i, j)) == SumL(s.subrange(i, j))
{
}

// ATOM 
proof fn equalSumsV()
    ensures forall |v: &[int], i: int, j: int| 0 <= i <= j <= v.len() ==> SumR(v@.subrange(i, j)) == SumL(v@.subrange(i, j))
{
}

// ATOM 
spec fn SumV(v: &[int], c: int, f: int) -> int
    recommends 0 <= c <= f <= v.len()
{
    SumR(v@.subrange(c, f))
}

// ATOM 
proof fn ArrayFacts<T>()
    ensures forall |v: &[T]| v@.subrange(0, v.len()) == v@
    ensures forall |v: &[T]| v@.subrange(0, v.len()) == v@
    ensures forall |v: &[T]| v@.subrange(0, v.len()) == v@
    ensures forall |v: &[T]| v@.subrange(0, v.len()).len() == v.len()
    ensures forall |v: &[T]| v.len() >= 1 ==> v@.subrange(1, v.len()).len() == v.len() - 1
    ensures forall |v: &[T], k: nat| k < v.len() ==> v@.subrange(0, k + 1).subrange(0, k) == v@.subrange(0, k)
{
}

// SPEC 
pub fn sumElems(v: &[int]) -> (sum: int)
    ensures sum == SumR(v@)
{
}

// SPEC 
pub fn sumElemsB(v: &[int]) -> (sum: int)
    ensures sum == SumR(v@.subrange(0, v.len()))
{
}