predicate ValidInput(n: int, s: string)
{
    n >= 1 && n <= 2000 && |s| == n && 
    forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOutput(result: string, n: int)
{
    |result| == n && 
    forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z'
}

predicate PreservesCharacters(s: string, result: string)
{
    multiset(s) == multiset(result)
}

// <vc-helpers>
lemma MultisetPreservesLength(s: string)
    ensures |s| == |multiset(s)|
{
}

lemma CharacterBoundsPreserved(s: string, result: string)
    requires multiset(s) == multiset(result)
    requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
    ensures forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z'
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
    requires ValidInput(n, s)
    ensures ValidOutput(result, n)
    ensures PreservesCharacters(s, result)
// </vc-spec>
// <vc-code>
{
    result := s;
}
// </vc-code>

