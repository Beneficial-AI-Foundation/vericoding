// ======= TASK =======
// Given n commentary boxes and m delegations, make the number of boxes divisible by m with minimum cost.
// You can build a box for cost a or demolish a box for cost b. Find the minimum total cost needed.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(n: int, m: int, a: int, b: int)
{
    n > 0 && m > 0 && a > 0 && b > 0
}

function MinCostToMakeDivisible(n: int, m: int, a: int, b: int): int
    requires ValidInput(n, m, a, b)
{
    var k := n % m;
    var demolishCost := k * b;
    var buildCost := (m - k) * a;
    if demolishCost <= buildCost then demolishCost else buildCost
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && 
    (s[0] != '-' || |s| > 1) &&
    forall i :: 0 <= i < |s| ==> (s[i] == '-' && i == 0) || ('0' <= s[i] <= '9')
}

function FindChar(s: string, c: char, start: int): int
    requires 0 <= start <= |s|
    ensures start <= FindChar(s, c, start) <= |s|
    ensures FindChar(s, c, start) == |s| ==> c !in s[start..]
    ensures FindChar(s, c, start) < |s| ==> s[FindChar(s, c, start)] == c
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == c then start
    else FindChar(s, c, start + 1)
}

function SplitStringFunc(s: string, delimiter: char): seq<string>
    requires |s| > 0
    ensures |SplitStringFunc(s, delimiter)| >= 1
    decreases |s|
{
    if delimiter !in s then [s]
    else 
        var i := FindChar(s, delimiter, 0);
        if i == 0 then 
            if |s| == 1 then [""]
            else SplitStringFunc(s[1..], delimiter)
        else [s[..i]] + (if i == |s| - 1 then [""] else SplitStringFunc(s[i+1..], delimiter))
}

function StringToIntFunc(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> (s[i] == '-' && i == 0) || ('0' <= s[i] <= '9')
{
    if s[0] == '-' then 
        if |s| == 1 then 0 else -StringToIntHelper(s[1..])
    else StringToIntHelper(s)
}

function StringToIntHelper(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToIntHelper(s) >= 0
    decreases |s|
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else StringToIntHelper(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function IntToStringFunc(n: int): string
    ensures |IntToStringFunc(n)| > 0
{
    if n == 0 then "0"
    else if n > 0 then IntToStringHelper(n)
    else "-" + IntToStringHelper(-n)
}

function IntToStringHelper(n: int): string
    requires n > 0
    ensures |IntToStringHelper(n)| > 0
    ensures forall i :: 0 <= i < |IntToStringHelper(n)| ==> '0' <= IntToStringHelper(n)[i] <= '9'
    decreases n
{
    if n < 10 then [('0' as int + n) as char]
    else IntToStringHelper(n / 10) + [('0' as int + n % 10) as char]
}

// <vc-helpers>
method SplitString(s: string, delimiter: char) returns (parts: seq<string>)
    requires |s| > 0
    ensures |parts| >= 1
    ensures parts == SplitStringFunc(s, delimiter)
{
    parts := SplitStringFunc(s, delimiter);
}

method StringToInt(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> (s[i] == '-' && i == 0) || ('0' <= s[i] <= '9')
    ensures s[0] != '-' ==> result >= 0
    ensures s[0] == '-' ==> result <= 0
    ensures result == StringToIntFunc(s)
{
    if s[0] == '-' {
        if |s| == 1 {
            result := 0;
        } else {
            var helper_result := StringToIntHelperMethod(s[1..]);
            result := -helper_result;
        }
    } else {
        result := StringToIntHelperMethod(s);
    }
}

method StringToIntHelperMethod(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result >= 0
    ensures result == StringToIntHelper(s)
{
    result := StringToIntHelper(s);
}

method IntToString(n: int) returns (result: string)
    ensures |result| > 0
    ensures n >= 0 ==> forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
    ensures n < 0 ==> result[0] == '-' && forall i :: 1 <= i < |result| ==> '0' <= result[i] <= '9'
    ensures result == IntToStringFunc(n)
{
    if n == 0 {
        result := "0";
    } else if n > 0 {
        result := IntToStringHelperMethod(n);
    } else {
        var pos_result := IntToStringHelperMethod(-n);
        result := "-" + pos_result;
    }
}

method IntToStringHelperMethod(n: int) returns (result: string)
    requires n > 0
    ensures |result| > 0
    ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
    ensures result == IntToStringHelper(n)
{
    result := IntToStringHelper(n);
}

lemma MinCostNonNegative(n: int, m: int, a: int, b: int)
    requires ValidInput(n, m, a, b)
    ensures MinCostToMakeDivisible(n, m, a, b) >= 0
{
    var k := n % m;
    var demolishCost := k * b;
    var buildCost := (m - k) * a;
    assert k >= 0;
    assert m - k >= 0;
    assert demolishCost >= 0;
    assert buildCost >= 0;
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires exists n, m, a, b :: 
        var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
        |trimmed| > 0 &&
        var parts := SplitStringFunc(trimmed, ' ');
        |parts| == 4 && 
        IsValidInteger(parts[0]) && IsValidInteger(parts[1]) && 
        IsValidInteger(parts[2]) && IsValidInteger(parts[3]) &&
        n == StringToIntFunc(parts[0]) && m == StringToIntFunc(parts[1]) && 
        a == StringToIntFunc(parts[2]) && b == StringToIntFunc(parts[3]) &&
        ValidInput(n, m, a, b)
    ensures |output| > 0
    ensures exists n, m, a, b ::
        var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
        var parts := SplitStringFunc(trimmed, ' ');
        n == StringToIntFunc(parts[0]) && m == StringToIntFunc(parts[1]) && 
        a == StringToIntFunc(parts[2]) && b == StringToIntFunc(parts[3]) &&
        ValidInput(n, m, a, b) &&
        var result := MinCostToMakeDivisible(n, m, a, b);
        result >= 0 &&
        output == IntToStringFunc(result)
// </vc-spec>
// <vc-code>
{
    var trimmed := input;
    if |trimmed| > 0 && trimmed[|trimmed|-1] == '\n' {
        trimmed := trimmed[..|trimmed|-1];
    }

    var parts := SplitString(trimmed, ' ');
    
    var n := StringToInt(parts[0]);
    var m := StringToInt(parts[1]);
    var a := StringToInt(parts[2]);
    var b := StringToInt(parts[3]);

    assert ValidInput(n, m, a, b);
    MinCostNonNegative(n, m, a, b);
    
    var result := MinCostToMakeDivisible(n, m, a, b);
    output := IntToString(result);
}
// </vc-code>

