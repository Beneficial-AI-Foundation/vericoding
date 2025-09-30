predicate ValidInput(s: string)
{
    |s| >= 4 && forall i :: 0 <= i < 4 ==> '0' <= s[i] <= '9'
}

function charPairToInt(c1: char, c2: char): int
    requires '0' <= c1 <= '9' && '0' <= c2 <= '9'
    ensures 0 <= charPairToInt(c1, c2) <= 99
{
    (c1 as int - '0' as int) * 10 + (c2 as int - '0' as int)
}

predicate ValidMonth(n: int)
{
    1 <= n <= 12
}

function GetFirstPair(s: string): int
    requires ValidInput(s)
    ensures 0 <= GetFirstPair(s) <= 99
{
    charPairToInt(s[0], s[1])
}

function GetSecondPair(s: string): int
    requires ValidInput(s)
    ensures 0 <= GetSecondPair(s) <= 99
{
    charPairToInt(s[2], s[3])
}

predicate CorrectResult(s: string, result: string)
    requires ValidInput(s)
{
    var s1 := GetFirstPair(s);
    var s2 := GetSecondPair(s);
    var s1_valid := ValidMonth(s1);
    var s2_valid := ValidMonth(s2);
    (s1_valid && s2_valid ==> result == "AMBIGUOUS\n") &&
    (s1_valid && !s2_valid ==> result == "MMYY\n") &&
    (!s1_valid && s2_valid ==> result == "YYMM\n") &&
    (!s1_valid && !s2_valid ==> result == "NA\n")
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures result in ["AMBIGUOUS\n", "MMYY\n", "YYMM\n", "NA\n"]
    ensures CorrectResult(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    var s1 := GetFirstPair(stdin_input);
    var s2 := GetSecondPair(stdin_input);
    var s1_valid := ValidMonth(s1);
    var s2_valid := ValidMonth(s2);
    
    if s1_valid && s2_valid {
        result := "AMBIGUOUS\n";
    } else if s1_valid && !s2_valid {
        result := "MMYY\n";
    } else if !s1_valid && s2_valid {
        result := "YYMM\n";
    } else {
        result := "NA\n";
    }
}
// </vc-code>

