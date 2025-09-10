function Max3(a: int, b: int, c: int): int
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

function CalculateMissedMeals(input: string): int
{
    var parts := SplitSpaces(TrimNewline(input));
    if |parts| >= 3 then
        var a := StringToInt(parts[0]);
        var b := StringToInt(parts[1]);  
        var c := StringToInt(parts[2]);
        var maxVal := Max3(a, b, c);
        var threshold := maxVal - 1;
        (if a < threshold then threshold - a else 0) +
        (if b < threshold then threshold - b else 0) +
        (if c < threshold then threshold - c else 0)
    else 0
}

predicate ValidInput(input: string)
{
    |input| > 0
}

// <vc-helpers>
predicate SplitSpacesValid(s: string)
{
    false  // Placeholder - not actually used
}

predicate StringToIntValid(s: string)
{
    false  // Placeholder - not actually used
}

lemma SplitSpacesPreservesContent(input: string)
{
}

lemma Max3Properties(a: int, b: int, c: int)
ensures Max3(a, b, c) >= a
ensures Max3(a, b, c) >= b
ensures Max3(a, b, c) >= c
{
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToString(-n)
    else var lastDigit := n % 10;
         var prefix := n / 10;
         (if prefix > 0 then IntToString(prefix) else "") + [('0' as int + lastDigit) as char]
}

function TrimNewline(s: string): string
{
    if |s| > 0 && (s[|s|-1] == '\n' || s[|s|-1] == '\r') then
        s[..|s|-1]
    else
        s
}

function SplitSpaces(s: string): seq<string>
{
    if s == "" then []
    else if s[0] == ' ' then SplitSpaces(s[1..])
    else
        var i := 0;
        while i < |s| && s[i] != ' '
            decreases |s| - i
        {
            i := i + 1;
        }
        [s[..i]] + SplitSpaces(s[i..])
}

function StringToInt(s: string): int
    requires |s| > 0
{
    if |s| == 1 then
        s[0] as int - '0' as int
    else
        StringToInt(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures result == IntToString(CalculateMissedMeals(input))
// </vc-spec>
// <vc-code>
{
    var trimmed := TrimNewline(input);
    var parts := SplitSpaces(trimmed);
    
    if |parts| >= 3 then
        var a := StringToInt(parts[0]);
        var b := StringToInt(parts[1]);
        var c := StringToInt(parts[2]);
        var maxVal := Max3(a, b, c);
        var threshold := maxVal - 1;
        var missed := (if a < threshold then threshold - a else 0) +
                     (if b < threshold then threshold - b else 0) +
                     (if c < threshold then threshold - c else 0);
        result := IntToString(missed);
    else
        result := "0";
}
// </vc-code>

