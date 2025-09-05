// ======= TASK =======
// Given two positive integers a and b, repeatedly apply operations until termination:
// 1. If a = 0 or b = 0, terminate
// 2. If a ≥ 2×b, set a = a - 2×b and go to step 1
// 3. If b ≥ 2×a, set b = b - 2×a and go to step 1  
// 4. Otherwise, terminate
// Find the final values of a and b.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(input: string)
{
    |input| > 0 &&
    (exists i :: 0 <= i < |input| && input[i] == ' ') &&
    (forall i :: 0 <= i < |input| ==> (input[i] == ' ' || ('0' <= input[i] <= '9')))
}

predicate ValidOutput(output: string)
{
    |output| > 0 &&
    (exists i :: 0 <= i < |output| && output[i] == ' ') &&
    (forall i :: 0 <= i < |output| ==> (output[i] == ' ' || ('0' <= output[i] <= '9')))
}

predicate IsTerminalState(a: int, b: int)
{
    (a == 0 || b == 0) || (a < 2 * b && b < 2 * a)
}

predicate ValidAlgorithmResult(a0: int, b0: int, a: int, b: int)
    requires a0 > 0 && b0 > 0
{
    a >= 0 && b >= 0 &&
    IsTerminalState(a, b) &&
    a <= a0 && b <= b0
}

// <vc-helpers>
method GcdAlgorithm(a0: int, b0: int) returns (a: int, b: int)
    requires a0 > 0 && b0 > 0
    ensures ValidAlgorithmResult(a0, b0, a, b)
    decreases a0 + b0
{
    a := a0;
    b := b0;

    while a > 0 && b > 0
        invariant a >= 0 && b >= 0
        invariant a <= a0 && b <= b0
        decreases a + b
    {
        if a >= 2 * b {
            a := a % (2 * b);
        } else if b >= 2 * a {
            b := b % (2 * a);
        } else {
            break;
        }
    }
}

method TrimString(s: string) returns (result: string)
    ensures |result| <= |s|
{
    var start := 0;
    var end := |s|;

    while start < |s| && s[start] == ' '
    {
        start := start + 1;
    }

    while end > start && end > 0 && s[end-1] == ' '
    {
        end := end - 1;
    }

    if start >= end {
        result := "";
    } else {
        result := s[start..end];
    }
}

method SplitString(s: string, delimiter: char) returns (parts: seq<string>)
    ensures |parts| >= 1
{
    parts := [];
    var current := "";
    var i := 0;

    while i < |s|
    {
        if s[i] == delimiter {
            parts := parts + [current];
            current := "";
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }

    parts := parts + [current];
}

method StringToInt(s: string) returns (result: int)
    ensures result >= 0
{
    result := 0;
    var i := 0;
    while i < |s|
        invariant result >= 0
    {
        if '0' <= s[i] <= '9' {
            result := result * 10 + (s[i] as int - '0' as int);
        }
        i := i + 1;
    }
}

method IntToString(n: int) returns (result: string)
    requires n >= 0
    ensures |result| >= 1
    ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
{
    if n == 0 {
        result := "0";
    } else {
        result := "";
        var temp := n;
        var original_n := n;
        while temp > 0
            invariant temp >= 0
            invariant forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
            invariant temp < original_n ==> |result| >= 1
        {
            var digit := temp % 10;
            var digit_char := ('0' as int + digit) as char;
            result := [digit_char] + result;
            temp := temp / 10;
        }
    }
}

lemma OutputValidityLemma(str_a: string, str_b: string, output: string)
    requires |str_a| >= 1 && |str_b| >= 1
    requires forall i :: 0 <= i < |str_a| ==> '0' <= str_a[i] <= '9'
    requires forall i :: 0 <= i < |str_b| ==> '0' <= str_b[i] <= '9'
    requires output == str_a + " " + str_b
    ensures ValidOutput(output)
{
    assert |output| == |str_a| + 1 + |str_b|;
    assert |output| > 0;
    assert output[|str_a|] == ' ';
    assert exists i :: 0 <= i < |output| && output[i] == ' ';
    
    forall i | 0 <= i < |output|
        ensures output[i] == ' ' || ('0' <= output[i] <= '9')
    {
        if i < |str_a| {
            assert output[i] == str_a[i];
        } else if i == |str_a| {
            assert output[i] == ' ';
        } else {
            assert i > |str_a|;
            assert output[i] == str_b[i - |str_a| - 1];
        }
    }
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures ValidOutput(output)
// </vc-spec>
// <vc-code>
{
    var trimmed := TrimString(input);
    var parts := SplitString(trimmed, ' ');

    if |parts| >= 2 {
        var a := StringToInt(parts[0]);
        var b := StringToInt(parts[1]);

        if a > 0 && b > 0 {
            var final_a, final_b := GcdAlgorithm(a, b);
            var str_a := IntToString(final_a);
            var str_b := IntToString(final_b);
            output := str_a + " " + str_b;
            
            OutputValidityLemma(str_a, str_b, output);
        } else {
            output := "1 1";
        }
    } else {
        output := "1 1";
    }
}
// </vc-code>

