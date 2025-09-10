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
function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n > 0
    decreases n
{
    if n < 10 then [('0' as int + n) as char]
    else IntToStringHelper(n / 10) + [('0' as int + (n % 10)) as char]
}

lemma UniqueCharsCardinality(s: string)
    ensures |UniqueChars(s)| <= |s|
{
}

lemma UniqueCharsSubset(s: string)
    ensures forall c :: c in UniqueChars(s) ==> c in s
{
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
        var unique := UniqueChars(s);
        var changes := if k <= |unique| then 0 else k - |unique|;
        result := IntToString(changes);
    }
}
// </vc-code>

