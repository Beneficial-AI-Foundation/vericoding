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
    ensures |SplitStringPure(s)| >= 1

predicate IsValidInt(s: string)

function StringToIntPure(s: string): int
    requires IsValidInt(s)

method SplitString(s: string) returns (parts: seq<string>)
    ensures parts == SplitStringPure(s)
    ensures |parts| >= 1

method IsValidIntMethod(s: string) returns (valid: bool)
    ensures valid == IsValidInt(s)

method StringToInt(s: string) returns (value: int)
    requires IsValidInt(s)
    ensures value == StringToIntPure(s)

lemma SameGroupEquivalence(a: int, b: int)
    ensures SameGroup(a, b) == ((a in [1, 3, 5, 7, 8, 10, 12] && b in [1, 3, 5, 7, 8, 10, 12]) || 
                                 (a in [4, 6, 9, 11] && b in [4, 6, 9, 11]) || 
                                 (a == 2 && b == 2))
{
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
    var parts := SplitString(input);
    
    if |parts| < 2 {
        result := "";
        return;
    }
    
    var valid1 := IsValidIntMethod(parts[0]);
    var valid2 := IsValidIntMethod(parts[1]);
    
    if !valid1 || !valid2 {
        result := "";
        return;
    }
    
    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    
    var n1 := [1, 3, 5, 7, 8, 10, 12];
    var n2 := [4, 6, 9, 11];
    
    SameGroupEquivalence(a, b);
    
    if (a in n1 && b in n1) || (a in n2 && b in n2) || (a == 2 && b == 2) {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

