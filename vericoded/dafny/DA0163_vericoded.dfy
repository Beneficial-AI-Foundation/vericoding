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
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else if n == 9 then "9"
    else if n == 10 then "10"
    else if n == 11 then "11"
    else if n == 12 then "12"
    else if n == 13 then "13"
    else if n == 14 then "14"
    else if n == 15 then "15"
    else if n == 16 then "16"
    else if n == 17 then "17"
    else if n == 18 then "18"
    else if n == 19 then "19"
    else if n == 20 then "20"
    else if n == 21 then "21"
    else if n == 22 then "22"
    else if n == 23 then "23"
    else if n == 24 then "24"
    else if n == 25 then "25"
    else if n == 26 then "26"
    else ""
}

method CountUniqueChars(s: string) returns (count: int)
    requires ValidInput(s, 1)
    ensures count == |UniqueChars(s)|
{
    var seen: set<char> := {};
    count := 0;
    
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant seen == set c | c in s[..i]
        invariant count == |seen|
    {
        if s[i] !in seen {
            seen := seen + {s[i]};
            count := count + 1;
        }
    }
    
    assert s[..|s|] == s;
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
        var uniqueCount := CountUniqueChars(s);
        var minChangesNeeded := if k <= uniqueCount then 0 else k - uniqueCount;
        result := IntToString(minChangesNeeded);
    }
}
// </vc-code>

