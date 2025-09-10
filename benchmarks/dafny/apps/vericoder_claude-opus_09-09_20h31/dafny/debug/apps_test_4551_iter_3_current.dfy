predicate ValidParseable(input: string)
{
    var parts := SplitStringPure(input);
    |parts| >= 4
}

predicate AllPartsAreIntegers(input: string)
{
    var parts := SplitStringPure(input);
    |parts| >= 4 &&
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1]) &&
    IsValidInteger(parts[2]) &&
    IsValidInteger(parts[3])
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> ('0' <= s[i] <= '9') || (i == 0 && s[i] == '-'))
}

predicate ValidParse(input: string, a: int, b: int, c: int, d: int)
{
    var parts := SplitStringPure(input);
    |parts| >= 4 && 
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1]) &&
    IsValidInteger(parts[2]) &&
    IsValidInteger(parts[3]) &&
    StringToIntPure(parts[0]) == a &&
    StringToIntPure(parts[1]) == b &&
    StringToIntPure(parts[2]) == c &&
    StringToIntPure(parts[3]) == d
}

function SplitStringPure(s: string): seq<string>
{
    SplitStringHelper(s, 0, "", [])
}

function SplitStringHelper(s: string, i: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if |current| > 0 then acc + [current] else acc
    else if s[i] == ' ' || s[i] == '\n' || s[i] == '\t' then
        if |current| > 0 then
            SplitStringHelper(s, i + 1, "", acc + [current])
        else
            SplitStringHelper(s, i + 1, "", acc)
    else
        SplitStringHelper(s, i + 1, current + [s[i]], acc)
}

function StringToIntPure(s: string): int
    requires IsValidInteger(s)
{
    if |s| > 0 && s[0] == '-' then
        -StringToIntHelperUnsigned(s, 1, 0)
    else
        StringToIntHelperUnsigned(s, 0, 0)
}

function StringToIntHelperUnsigned(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then acc
    else if '0' <= s[i] <= '9' then
        StringToIntHelperUnsigned(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else
        acc
}

// <vc-helpers>
method SplitString(s: string) returns (parts: seq<string>)
    ensures parts == SplitStringPure(s)
{
    var i := 0;
    var current := "";
    parts := [];
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant parts + (if |current| > 0 then [current] else []) == SplitStringHelper(s, i, current, parts)
    {
        if s[i] == ' ' || s[i] == '\n' || s[i] == '\t' {
            if |current| > 0 {
                parts := parts + [current];
                current := "";
            }
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }
    
    if |current| > 0 {
        parts := parts + [current];
    }
}

method StringToInt(s: string) returns (n: int)
    requires IsValidInteger(s)
    ensures n == StringToIntPure(s)
{
    if |s| > 0 && s[0] == '-' {
        if |s| == 1 {
            // Just a '-' is not valid according to IsValidInteger
            // This case should not occur due to the precondition
            n := 0;
            assert false; // This branch is unreachable given the precondition
        } else {
            var unsigned := StringToIntUnsigned(s[1..]);
            n := -unsigned;
            assert n == -StringToIntHelperUnsigned(s[1..], 0, 0);
            assert n == -StringToIntHelperUnsigned(s, 1, 0);
        }
    } else {
        n := StringToIntUnsigned(s);
        assert n == StringToIntHelperUnsigned(s, 0, 0);
    }
}

method StringToIntUnsigned(s: string) returns (n: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures n == StringToIntHelperUnsigned(s, 0, 0)
{
    var i := 0;
    n := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant n == StringToIntHelperUnsigned(s, 0, 0) - StringToIntHelperUnsigned(s, i, 0) + StringToIntHelperUnsigned(s, i, n)
        invariant StringToIntHelperUnsigned(s, i, n) == StringToIntHelperUnsigned(s, i, 0) + n
    {
        n := n * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    
    assert i == |s|;
    assert StringToIntHelperUnsigned(s, |s|, n) == n;
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures (forall a, b, c, d: int :: 
        ValidParse(input, a, b, c, d) ==> 
        (result == "Left\n" <==> a + b > c + d) &&
        (result == "Right\n" <==> a + b < c + d) &&
        (result == "Balanced\n" <==> a + b == c + d))
    ensures ValidParseable(input) && AllPartsAreIntegers(input) ==> (result == "Left\n" || result == "Right\n" || result == "Balanced\n")
    ensures (!ValidParseable(input) || !AllPartsAreIntegers(input)) ==> result == ""
// </vc-spec>
// <vc-code>
{
    var parts := SplitString(input);
    
    if |parts| < 4 {
        return "";
    }
    
    if !IsValidInteger(parts[0]) || !IsValidInteger(parts[1]) || 
       !IsValidInteger(parts[2]) || !IsValidInteger(parts[3]) {
        return "";
    }
    
    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    var c := StringToInt(parts[2]);
    var d := StringToInt(parts[3]);
    
    var leftSum := a + b;
    var rightSum := c + d;
    
    if leftSum > rightSum {
        result := "Left\n";
    } else if leftSum < rightSum {
        result := "Right\n";
    } else {
        result := "Balanced\n";
    }
}
// </vc-code>

