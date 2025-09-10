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
lemma SplitStringPureLength(s: string)
    ensures |SplitStringPure(s)| >= 2 ==> |s| > 0

lemma StringToIntPureValid(s: string)
    requires IsValidInt(s)
    ensures StringToIntPure(s) >= 1 && StringToIntPure(s) <= 12

function method SplitStringPure(s: string): seq<string>
    ensures |s| > 0 ==> |result| >= 1

predicate IsValidInt(s: string)
    ensures IsValidInt(s) ==> (s != "" && (forall i | 0 <= i < |s| :: '0' <= s[i] <= '9'))

lemma SplitStringPartsValid(input: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures |SplitStringPure(input)| >= 2 &&
        IsValidInt(SplitStringPure(input)[0]) &&
        IsValidInt(SplitStringPure(input)[1])
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
    
    if !IsValidInt(parts[0]) || !IsValidInt(parts[1]) {
        result := "";
        return;
    }
    
    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    
    if (a < 1 || a > 12) || (b < 1 || b > 12) {
        result := "";
        return;
    }
    
    var n1 : set<int> := {1, 3, 5, 7, 8, 10, 12};
    var n2 : set<int> := {4, 6, 9, 11};
    
    if (a in n1 && b in n1) || (a in n2 && b in n2) || (a == 2 && b == 2) {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

