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
function IsArithmeticProgression(a: int, b: int, c: int): bool {
  b - a == c - b
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
    var parts := SplitBySpacesFunc(input);
    if |parts| == 3 && IsValidInteger(parts[0]) && IsValidInteger(parts[1]) && IsValidInteger(parts[2])
    {
        var a := ParseIntFunc(parts[0]);
        var b := ParseIntFunc(parts[1]);
        var c := ParseIntFunc(parts[2]);
        
        // This lemma implies that if ValidThreeIntegers holds for some (a,b,c),
        // then ParseIntFunc applied to the parts from SplitBySpacesFunc(input)
        // will yield those same a, b, c. This helps prove the uniqueness
        // and correctness of a, b, c.
        if ValidThreeIntegers(input, a, b, c)
        {
             if IsArithmeticProgression(a, b, c) then
                return "YES\n";
            else
                return "NO\n";
        }
        else
        {
            // This case should ideally not be reached if the preconditions truly imply ValidThreeIntegers (a,b,c),
            // due to ParseIntFunc(parts[0]) == a etc.
            // However, Dafny might need an explicit `else` branch for totality or clarity.
            return ""; // Should not happen based on the `if` condition.
        }
    }
    else
    {
        return "";
    }
}
// </vc-code>

