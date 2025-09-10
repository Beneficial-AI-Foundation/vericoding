predicate ValidThreeIntegers(input: string, a: int, b: int, c: int)
{
    var parts := SplitBySpacesFunc(input);
    |parts| == 3 && 
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1]) &&
    IsValidInteger(parts[2]) &&
    ParseIntFunc(parts[0]) == a &&
    ParseIntFunc(parts[1]) == b &&
    ParseIntFunc(parts[2]) == c
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && 
    (s[0] != '-' || |s| > 1) &&
    (s[0] == '-' ==> forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9') &&
    (s[0] != '-' ==> forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function SplitBySpacesFunc(s: string): seq<string>
{
    SplitBySpacesHelper(s, 0, "", [])
}

function SplitBySpacesHelper(s: string, i: int, current: string, parts: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if |current| > 0 then parts + [current] else parts
    else if s[i] == ' ' || s[i] == '\n' || s[i] == '\t' then
        if |current| > 0 then
            SplitBySpacesHelper(s, i + 1, "", parts + [current])
        else
            SplitBySpacesHelper(s, i + 1, current, parts)
    else
        SplitBySpacesHelper(s, i + 1, current + [s[i]], parts)
}

function ParseIntFunc(s: string): int
    requires |s| > 0
    requires IsValidInteger(s)
{
    if |s| > 0 && s[0] == '-' then
        -ParseUnsignedInt(s[1..])
    else
        ParseUnsignedInt(s)
}

function ParseUnsignedInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 0 then 0
    else ParseUnsignedInt(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

// <vc-helpers>
method SplitBySpaces(s: string) returns (parts: seq<string>)
    ensures parts == SplitBySpacesFunc(s)
{
    parts := [];
    var current := "";
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant SplitBySpacesHelper(s, 0, "", []) == SplitBySpacesHelper(s, i, current, parts)
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

method ParseInt(s: string) returns (value: int, success: bool)
    requires |s| > 0
    ensures success ==> IsValidInteger(s) && value == ParseIntFunc(s)
    ensures !success ==> !IsValidInteger(s)
{
    var isNegative := s[0] == '-';
    var startIdx := if isNegative then 1 else 0;
    
    if isNegative && |s| == 1 {
        success := false;
        value := 0;
        return;
    }
    
    var i := startIdx;
    while i < |s|
        invariant startIdx <= i <= |s|
        invariant forall j :: startIdx <= j < i ==> '0' <= s[j] <= '9'
    {
        if !(s[i] >= '0' && s[i] <= '9') {
            success := false;
            value := 0;
            return;
        }
        i := i + 1;
    }
    
    value := 0;
    i := startIdx;
    while i < |s|
        invariant startIdx <= i <= |s|
        invariant forall j :: startIdx <= j < |s| ==> '0' <= s[j] <= '9'
        invariant value == ParseUnsignedInt(s[startIdx..i])
        invariant s[startIdx..i] == s[startIdx..][..i-startIdx]
    {
        assert s[startIdx..i+1] == s[startIdx..i] + [s[i]];
        value := value * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    
    if isNegative {
        value := -value;
    }
    
    success := true;
    assert IsValidInteger(s);
    if isNegative {
        assert value == -ParseUnsignedInt(s[1..]);
        assert value == ParseIntFunc(s);
    } else {
        assert s[startIdx..] == s;
        assert value == ParseUnsignedInt(s);
        assert value == ParseIntFunc(s);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures (exists a: int, b: int, c: int :: ValidThreeIntegers(input, a, b, c)) ==> 
            (result == "YES\n" || result == "NO\n")
    ensures (exists a: int, b: int, c: int :: ValidThreeIntegers(input, a, b, c)) ==> 
            (exists a: int, b: int, c: int :: ValidThreeIntegers(input, a, b, c) && 
             (result == "YES\n" <==> b - a == c - b))
    ensures !(exists a: int, b: int, c: int :: ValidThreeIntegers(input, a, b, c)) ==> 
            result == ""
    ensures (forall a1: int, b1: int, c1: int, a2: int, b2: int, c2: int ::
        ValidThreeIntegers(input, a1, b1, c1) && ValidThreeIntegers(input, a2, b2, c2) ==>
        a1 == a2 && b1 == b2 && c1 == c2)
// </vc-spec>
// <vc-code>
{
    var parts := SplitBySpaces(input);
    
    if |parts| != 3 {
        return "";
    }
    
    if |parts[0]| == 0 || |parts[1]| == 0 || |parts[2]| == 0 {
        return "";
    }
    
    var a, successA := ParseInt(parts[0]);
    if !successA {
        return "";
    }
    
    var b, successB := ParseInt(parts[1]);
    if !successB {
        return "";
    }
    
    var c, successC := ParseInt(parts[2]);
    if !successC {
        return "";
    }
    
    assert ValidThreeIntegers(input, a, b, c);
    
    if b - a == c - b {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
}
// </vc-code>

