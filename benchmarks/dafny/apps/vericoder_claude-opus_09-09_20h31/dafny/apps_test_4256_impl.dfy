predicate ValidInput(input: string)
{
    |input| > 0 &&
    exists i, j :: 0 <= i < j < |input| && input[i] == ' ' && input[j] == ' ' &&
    (
        var parts := SplitStringSpec(input);
        |parts| >= 3 && 
        IsValidInteger(parts[0]) && IsValidInteger(parts[1]) && IsValidInteger(parts[2]) &&
        var A := StringToIntSpec(parts[0]);
        var B := StringToIntSpec(parts[1]);
        var C := StringToIntSpec(parts[2]);
        1 <= A <= 100 && 1 <= B <= 100 && 1 <= C <= 100
    )
}

function ComputeDrinks(A: int, B: int, C: int): int
    requires A >= 1 && B >= 1 && C >= 1
{
    if B / A < C then B / A else C
}

function IsValidInteger(s: string): bool
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToIntSpec(s: string): int
    requires IsValidInteger(s)
    ensures StringToIntSpec(s) >= 0
{
    if |s| == 1 then s[0] as int - '0' as int
    else StringToIntSpec(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function SplitStringSpec(s: string): seq<string>
    ensures forall i :: 0 <= i < |SplitStringSpec(s)| ==> |SplitStringSpec(s)[i]| > 0
    ensures forall i :: 0 <= i < |SplitStringSpec(s)| ==> forall j :: 0 <= j < |SplitStringSpec(s)[i]| ==> SplitStringSpec(s)[i][j] != ' ' && SplitStringSpec(s)[i][j] != '\n' && SplitStringSpec(s)[i][j] != '\t'
{
    if |s| == 0 then []
    else 
        var parts := SplitHelper(s, 0, "");
        parts
}

function SplitHelper(s: string, index: int, current: string): seq<string>
    requires 0 <= index <= |s|
    requires forall j :: 0 <= j < |current| ==> current[j] != ' ' && current[j] != '\n' && current[j] != '\t'
    decreases |s| - index
    ensures forall i :: 0 <= i < |SplitHelper(s, index, current)| ==> |SplitHelper(s, index, current)[i]| > 0
    ensures forall i :: 0 <= i < |SplitHelper(s, index, current)| ==> forall j :: 0 <= j < |SplitHelper(s, index, current)[i]| ==> SplitHelper(s, index, current)[i][j] != ' ' && SplitHelper(s, index, current)[i][j] != '\n' && SplitHelper(s, index, current)[i][j] != '\t'
{
    if index >= |s| then
        if |current| > 0 then [current] else []
    else if s[index] == ' ' || s[index] == '\n' || s[index] == '\t' then
        if |current| > 0 then [current] + SplitHelper(s, index + 1, "")
        else SplitHelper(s, index + 1, "")
    else
        SplitHelper(s, index + 1, current + [s[index]])
}

function IntToStringSpec(n: int): string
    requires n >= 0
    ensures |IntToStringSpec(n)| > 0
    ensures forall i :: 0 <= i < |IntToStringSpec(n)| ==> '0' <= IntToStringSpec(n)[i] <= '9'
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else IntToStringSpec(n / 10) + [('0' as int + (n % 10)) as char]
}

// <vc-helpers>
method SplitString(s: string) returns (parts: seq<string>)
    ensures parts == SplitStringSpec(s)
{
    parts := [];
    var current := "";
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < |current| ==> current[j] != ' ' && current[j] != '\n' && current[j] != '\t'
        invariant parts + SplitHelper(s, i, current) == SplitStringSpec(s)
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

lemma StringToIntEmpty()
    ensures IsValidInteger("") == false
{}

lemma StringToIntSubstring(s: string, i: int)
    requires IsValidInteger(s)
    requires 0 <= i <= |s|
    ensures i == 0 ==> s[..i] == ""
    ensures i > 0 ==> IsValidInteger(s[..i])
{}

lemma StringToIntSingleChar(s: string)
    requires IsValidInteger(s)
    requires |s| >= 1
    ensures StringToIntSpec(s[..1]) == s[0] as int - '0' as int
{
    assert s[..1] == [s[0]];
}

method StringToInt(s: string) returns (n: int)
    requires IsValidInteger(s)
    ensures n == StringToIntSpec(s)
{
    n := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant i == 0 ==> n == 0
        invariant i > 0 ==> n == StringToIntSpec(s[..i])
    {
        if i == 0 {
            n := s[0] as int - '0' as int;
            StringToIntSingleChar(s);
        } else {
            assert s[..i+1] == s[..i] + [s[i]];
            n := n * 10 + (s[i] as int - '0' as int);
        }
        i := i + 1;
    }
    assert s[..|s|] == s;
}

function ReverseString(s: string): string
{
    if |s| == 0 then ""
    else ReverseString(s[1..]) + [s[0]]
}

function BuildIntString(n: int, acc: string): string
    requires n >= 0
    ensures |BuildIntString(n, acc)| >= |acc|
    ensures forall k :: 0 <= k < |BuildIntString(n, acc)| ==> '0' <= BuildIntString(n, acc)[k] <= '9'
{
    if n == 0 then
        if |acc| == 0 then "0" else acc
    else
        var digit := n % 10;
        BuildIntString(n / 10, [('0' as int + digit) as char] + acc)
}

lemma IntToStringEquivalence(n: int)
    requires n >= 0
    ensures BuildIntString(n, "") == IntToStringSpec(n)
{
}

method IntToString(n: int) returns (s: string)
    requires n >= 0
    ensures s == IntToStringSpec(n)
{
    if n == 0 {
        s := "0";
        return;
    }
    
    s := "";
    var temp := n;
    
    while temp > 0
        invariant 0 <= temp <= n
        invariant |s| >= 0
        invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
        invariant BuildIntString(temp, s) == IntToStringSpec(n)
        decreases temp
    {
        var digit := temp % 10;
        s := [('0' as int + digit) as char] + s;
        temp := temp / 10;
    }
    
    assert temp == 0;
    assert BuildIntString(0, s) == s;
    IntToStringEquivalence(n);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures (
        var parts := SplitStringSpec(input);
        var A := StringToIntSpec(parts[0]);
        var B := StringToIntSpec(parts[1]);
        var C := StringToIntSpec(parts[2]);
        var drinks := ComputeDrinks(A, B, C);
        result == IntToStringSpec(drinks) + "\n"
    )
// </vc-spec>
// <vc-code>
{
    var parts := SplitString(input);
    
    var A := StringToInt(parts[0]);
    var B := StringToInt(parts[1]);
    var C := StringToInt(parts[2]);
    
    var drinks := ComputeDrinks(A, B, C);
    
    var drinkStr := IntToString(drinks);
    result := drinkStr + "\n";
}
// </vc-code>

