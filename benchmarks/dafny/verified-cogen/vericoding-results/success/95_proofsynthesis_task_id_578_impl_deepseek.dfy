// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
function max(a: int, b: int): int { if a > b then a else b }
predicate ValidIndex(i: int, len: int) { 0 <= i < len }
// </vc-helpers>

// <vc-spec>
method interleave(s1: array<int>, s2: array<int>, s3: array<int>) returns (res: array<int>)
    requires s1.Length == s2.Length && s2.Length == s3.Length
    requires 0 <= (s1.Length * 3)
    ensures res.Length == s1.Length * 3
    ensures forall i :: 0 <= i < s1.Length ==> (res[3 * i] == s1[i] && res[3 * i + 1] == s2[i] && res[3 * i + 2] == s3[i])
// </vc-spec>
// <vc-code>
{
    var len := s1.Length;
    res := new int[len * 3];
    var index := 0;
    
    var i := 0;
    while i < len
        invariant 0 <= i <= len
        invariant index == 3 * i
        invariant forall j :: 0 <= j < i ==> (res[3 * j] == s1[j] && res[3 * j + 1] == s2[j] && res[3 * j + 2] == s3[j])
    {
        res[index] := s1[i];
        res[index + 1] := s2[i];
        res[index + 2] := s3[i];
        index := index + 3;
        i := i + 1;
    }
}
// </vc-code>
