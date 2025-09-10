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

// <vc-helpers>
function IntToString(n: nat): string
{
    if n == 0 then "0" else IntToStringPos(n)
}

function IntToStringPos(n: nat): string
    requires n > 0
{
    if n < 10 then [(n + '0')]
    else IntToStringPos(n / 10) + [(n % 10 + '0')]
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: string)
    requires ValidInput(s, k)
    ensures IsImpossible(s, k) ==> result == "impossible"
    ensures !IsImpossible(s, k) ==> result == IntToString(MinChanges(s, k))
// </vc-spec>
// <vc-code>
{
    if |s| < k {
        result := "impossible";
    } else {
        var chrs := UniqueChars(s);
        var changes := if k <= |chrs| then 0 else k - |chrs|;
        result := IntToString(changes);
    }
}
// </vc-code>

