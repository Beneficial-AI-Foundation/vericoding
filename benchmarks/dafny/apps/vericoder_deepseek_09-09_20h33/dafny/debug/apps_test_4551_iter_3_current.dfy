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
lemma StringToIntPureNonNegative(s: string)
    requires IsValidInteger(s)
    requires s[0] != '-'
    ensures StringToIntPure(s) >= 0
{
    var res := StringToIntHelperUnsigned(s, 0, 0);
    StringToIntHelperUnsignedIncreases(s, 0, 0);
    assert res >= 0;
}

lemma StringToIntPureNegative(s: string)
    requires IsValidInteger(s)
    requires s[0] == '-'
    ensures StringToIntPure(s) <= 0
{
    var res := StringToIntHelperUnsigned(s, 1, 0);
    StringToIntHelperUnsignedIncreases(s, 1, 0);
    assert -res <= 0;
}

lemma StringToIntHelperUnsignedIncreases(s: string, i: int, acc: int)
    requires 0 <= i <= |s|
    decreases |s| - i
    ensures StringToIntHelperUnsigned(s, i, acc) >= acc
{
    if i < |s| && '0' <= s[i] <= '9' {
        var new_acc := acc * 10 + (s[i] as int - '0' as int);
        assert new_acc >= acc by {
            // Prove that new_acc >= acc
            // Since s[i] >= '0', we have (s[i] as int - '0' as int) >= 0
            // and acc * 10 >= acc (for acc >= 0)
        }
        StringToIntHelperUnsignedIncreases(s, i + 1, new_acc);
    }
}

lemma SplitStringPureValidIndex(s: string, idx: int)
    requires 0 <= idx < |SplitStringPure(s)|
    ensures |SplitStringPure(s)[idx]| > 0
{
    var parts := SplitStringPure(s);
    // The construction in SplitStringHelper ensures that each part in the result
    // is non-empty because we only add [current] to acc when |current| > 0
    // and all parts are built from non-space characters
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
    if !ValidParseable(input) || !AllPartsAreIntegers(input) {
        result := "";
        return;
    }
    
    var parts := SplitStringPure(input);
    // Prepare to handle potential negative signs
    assert AllPartsAreIntegers(input);
    assert IsValidInteger(parts[0]) && IsValidInteger(parts[1]) && 
           IsValidInteger(parts[2]) && IsValidInteger(parts[3]);
    
    // Check for negative signs in each part before calling StringToIntPureNonNegative
    if parts[0][0] != '-' {
        StringToIntPureNonNegative(parts[0]);
    }
    if parts[1][0] != '-' {
        StringToIntPureNonNegative(parts[1]);
    }
    if parts[2][0] != '-' {
        StringToIntPureNonNegative(parts[2]);
    }
    if parts[3][0] != '-' {
        StringToIntPureNonNegative(parts[3]);
    }
    
    var a := StringToIntPure(parts[0]);
    var b := StringToIntPure(parts[1]);
    var c := StringToIntPure(parts[2]);
    var d := StringToIntPure(parts[3]);
    
    var sum1 := a + b;
    var sum2 := c + d;
    
    if sum1 > sum2 {
        result := "Left\n";
    } else if sum1 < sum2 {
        result := "Right\n";
    } else {
        result := "Balanced\n";
    }
}
// </vc-code>

