predicate ValidInput(input: string)
    requires |input| > 0
{
    var parts := SplitStringPure(input);
    |parts| >= 2 && IsValidInt(parts[0]) && IsValidInt(parts[1])
}

predicate SameGroup(a: int, b: int)
{
    var n1 := [1, 3, 5, 7, 8, 10, 12];
    var n2 := [4, 6, 9, 11];
    (a in n1 && b in n1) || (a in n2 && b in n2) || (a == 2 && b == 2)
}

predicate CorrectOutput(input: string, result: string)
    requires |input| > 0
{
    if ValidInput(input) then
        var parts := SplitStringPure(input);
        var a := StringToIntPure(parts[0]);
        var b := StringToIntPure(parts[1]);
        (result == "Yes\n" <==> SameGroup(a, b)) && (result == "No\n" <==> !SameGroup(a, b))
    else
        result == ""
}

// <vc-helpers>
function SplitStringPure(s: string): seq<string>
{
    SplitString(s)
}

function SplitString(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == ' ' then SplitString(s[1..])
    else 
        var end := FindSpace(s, 0);
        if end == |s| then [s]
        else [s[..end]] + SplitString(s[end+1..])
}

function FindSpace(s: string, i: nat): nat
    requires i <= |s|
    ensures FindSpace(s, i) <= |s|
{
    if i == |s| then i
    else if s[i] == ' ' then i
    else FindSpace(s, i + 1)
}

predicate IsValidInt(s: string)
{
    |s| > 0 && 
    (s[0] == '-' ==> |s| > 1 && forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9') &&
    (s[0] != '-' ==> forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function StringToIntPure(s: string): int
    requires IsValidInt(s)
{
    StringToInt(s)
}

function StringToInt(s: string): int
    requires IsValidInt(s)
{
    if s[0] == '-' then -StringToNat(s[1..])
    else StringToNat(s)
}

function StringToNat(s: string): nat
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else StringToNat(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

method ParseInput(input: string) returns (valid: bool, a: int, b: int)
    requires |input| > 0
    ensures valid == ValidInput(input)
    ensures valid ==> 
        var parts := SplitStringPure(input);
        a == StringToIntPure(parts[0]) && b == StringToIntPure(parts[1])
{
    var parts := SplitStringMethod(input);
    if |parts| >= 2 && IsValidIntMethod(parts[0]) && IsValidIntMethod(parts[1]) {
        valid := true;
        a := StringToIntMethod(parts[0]);
        b := StringToIntMethod(parts[1]);
    } else {
        valid := false;
        a := 0;
        b := 0;
    }
}

method SplitStringMethod(s: string) returns (parts: seq<string>)
    ensures parts == SplitStringPure(s)
{
    parts := [];
    var i := 0;
    var start := 0;
    
    // Skip leading spaces
    while i < |s| && s[i] == ' '
        invariant 0 <= i <= |s|
    {
        i := i + 1;
        start := i;
    }
    
    while i < |s|
        invariant 0 <= start <= i <= |s|
    {
        if s[i] == ' ' {
            if start < i {
                parts := parts + [s[start..i]];
            }
            i := i + 1;
            // Skip consecutive spaces
            while i < |s| && s[i] == ' '
                invariant start <= i <= |s|
            {
                i := i + 1;
            }
            start := i;
        } else {
            i := i + 1;
        }
    }
    
    if start < i {
        parts := parts + [s[start..i]];
    }
}

method IsValidIntMethod(s: string) returns (valid: bool)
    ensures valid == IsValidInt(s)
{
    if |s| == 0 {
        return false;
    }
    
    var start := 0;
    if s[0] == '-' {
        if |s| == 1 {
            return false;
        }
        start := 1;
    }
    
    var i := start;
    while i < |s|
        invariant start <= i <= |s|
        invariant forall j :: start <= j < i ==> '0' <= s[j] <= '9'
    {
        if s[i] < '0' || s[i] > '9' {
            return false;
        }
        i := i + 1;
    }
    
    return true;
}

method StringToIntMethod(s: string) returns (result: int)
    requires IsValidInt(s)
    ensures result == StringToIntPure(s)
{
    if s[0] == '-' {
        var n := StringToNatMethod(s[1..]);
        result := -n;
    } else {
        result := StringToNatMethod(s);
    }
}

method StringToNatMethod(s: string) returns (result: nat)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result == StringToNat(s)
{
    result := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result == StringToNat(s[..i])
    {
        result := result * 10 + ((s[i] as int) - ('0' as int));
        i := i + 1;
    }
}

method CheckSameGroup(a: int, b: int) returns (same: bool)
    ensures same == SameGroup(a, b)
{
    var n1 := [1, 3, 5, 7, 8, 10, 12];
    var n2 := [4, 6, 9, 11];
    
    var inN1_a := a in n1;
    var inN1_b := b in n1;
    var inN2_a := a in n2;
    var inN2_b := b in n2;
    
    same := (inN1_a && inN1_b) || (inN2_a && inN2_b) || (a == 2 && b == 2);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == "Yes\n" || result == "No\n" || result == ""
    ensures CorrectOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var valid, a, b := ParseInput(input);
    
    if !valid {
        result := "";
    } else {
        var same := CheckSameGroup(a, b);
        if same {
            result := "Yes\n";
        } else {
            result := "No\n";
        }
    }
}
// </vc-code>

