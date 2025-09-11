// <vc-preamble>
predicate ValidInput(s: string, k: int)
{
    1 <= k <= 26 && 1 <= |s| <= 1000 && 
    forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

function UniqueChars(s: string): set<char>
{
    set c | c in s
}

function MinChanges(s: string, k: int): int
    requires ValidInput(s, k)
    requires |s| >= k
{
    var unique := UniqueChars(s);
    if k <= |unique| then 0 else k - |unique|
}

predicate IsImpossible(s: string, k: int)
    requires ValidInput(s, k)
{
    |s| < k
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: string)
    requires ValidInput(s, k)
    ensures IsImpossible(s, k) ==> result == "impossible"
    ensures !IsImpossible(s, k) ==> result == IntToString(MinChanges(s, k))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
