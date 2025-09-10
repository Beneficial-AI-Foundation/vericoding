predicate ValidInput(input: string)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B))
}

function ContestStartTime(A: int, B: int): int
    requires 0 <= A <= 23 && 0 <= B <= 23
    ensures 0 <= ContestStartTime(A, B) <= 23
{
    (A + B) % 24
}

predicate CorrectOutput(input: string, result: string)
    requires ValidInput(input)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B)) &&
    result == IntToString(ContestStartTime(A, B)) + "\n"
}

// <vc-helpers>
function StringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then
        (s[0] as int) - ('0' as int)
    else
        StringToInt(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function IntToString(n: int): string
    requires 0 <= n
    decreases n
{
    if n < 10 then
        [(n + ('0' as int)) as char]
    else
        IntToString(n / 10) + [(n % 10 + ('0' as int)) as char]
}

lemma IntToStringToInt(n: int)
    requires 0 <= n
    ensures |IntToString(n)| > 0
    ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
    ensures StringToInt(IntToString(n)) == n
{
    if n < 10 {
        assert IntToString(n) == [(n + ('0' as int)) as char];
    } else {
        IntToStringToInt(n / 10);
        var prefix := IntToString(n / 10);
        var lastDigit := (n % 10 + ('0' as int)) as char;
        assert IntToString(n) == prefix + [lastDigit];
    }
}

function FindSpace(s: string): int
    requires |s| > 0
    ensures 0 <= FindSpace(s) <= |s|
    ensures FindSpace(s) < |s| ==> s[FindSpace(s)] == ' '
    ensures forall i :: 0 <= i < FindSpace(s) ==> s[i] != ' '
{
    if s[0] == ' ' then 0
    else if |s| == 1 then |s|
    else 1 + FindSpace(s[1..])
}

predicate IsDigitString(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var spaceIndex := FindSpace(input);
    if spaceIndex == |input| {
        return "Invalid input\n";
    }
    
    var firstPart := input[..spaceIndex];
    var remaining := input[spaceIndex+1..];
    
    if !IsDigitString(firstPart) || |remaining| == 0 {
        return "Invalid input\n";
    }
    
    var secondPart: string;
    if |remaining| > 0 && remaining[|remaining|-1] == '\n' {
        secondPart := remaining[..|remaining|-1];
    } else {
        secondPart := remaining;
    }
    
    if !IsDigitString(secondPart) {
        return "Invalid input\n";
    }
    
    var A := StringToInt(firstPart);
    var B := StringToInt(secondPart);
    
    if !(0 <= A <= 23 && 0 <= B <= 23) {
        return "Invalid input\n";
    }
    
    IntToStringToInt(A);
    IntToStringToInt(B);
    
    var startTime := ContestStartTime(A, B);
    IntToStringToInt(startTime);
    
    result := IntToString(startTime) + "\n";
}
// </vc-code>

