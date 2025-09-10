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
        invariant parts + (if |current| > 0 then [current] else []) + SplitHelper(s, i, current) == SplitStringSpec(s)
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
    ensures n == StringToIntSpec(s)
{
    n := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> '0' <= s[k] <= '9'
        invariant if i == 0 then n == 0 else n == StringToIntSpec(s[..i])
    {
        n := n * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
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
    var original := n;
    
    while temp > 0
        invariant 0 <= temp <= original
        invariant original == n
        invariant temp == 0 ==> s == IntToStringSpec(n)
        invariant temp > 0 ==> s == IntToStringSpec(n - n % (temp * 10)) && n % (temp * 10) == temp + (n % temp)
        decreases temp
    {
        var digit := temp % 10;
        s := [('0' as int + digit) as char] + s;
        temp := temp / 10;
    }
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

