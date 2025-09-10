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
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures result == IntToString(CalculateMissedMeals(input))
// </vc-spec>
// <vc-code>
{
    // Parse input string manually since helper functions don't exist
    var i := 0;
    var a_val := 0;
    var b_val := 0;
    var c_val := 0;
    var count := 0;
    var current := 0;
    
    while i < |input| && count < 3
        decreases |input| - i
    {
        var ch := input[i];
        if ch == ' ' || ch == '\n' || ch == '\r' {
            if count == 0 { a_val := current; }
            else if count == 1 { b_val := current; }
            count := count + 1;
            current := 0;
        } else if '0' <= ch && ch <= '9' {
            current := current * 10 + (ch as int - '0' as int);
        }
        i := i + 1;
    }
    
    if count == 2 {
        c_val := current;
    }
    
    if count == 2 {
        var max_val := Max3(a_val, b_val, c_val);
        var threshold := max_val - 1;
        var missed1 := if a_val < threshold then threshold - a_val else 0;
        var missed2 := if b_val < threshold then threshold - b_val else 0;
        var missed3 := if c_val < threshold then threshold - c_val else 0;
        result := IntToString(missed1 + missed2 + missed3);
    } else {
        result := "0";
    }
}
// </vc-code>

