predicate ValidInput(a: int, b: int, c: int)
{
    1 <= b <= a <= 20 && 1 <= c <= 20
}

function RemainingWater(a: int, b: int, c: int): int
    requires ValidInput(a, b, c)
{
    var availableSpace := a - b;
    var remaining := c - availableSpace;
    if remaining >= 0 then remaining else 0
}

// <vc-helpers>
function method SplitOnSpaces(s: string): seq<string>
    ensures |SplitOnSpaces(s)| > 0

function method StringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'

function method IntToString(n: int): string

lemma SplitOnSpacesProperties(s: string)
    requires |s| > 0
    ensures var parts := SplitOnSpaces(s);
             |parts| == 3 ==>
             (forall i :: 0 <= i < |parts| && i < 3 ==> |parts[i]| > 0) &&
             (forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9') &&
             (forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9') &&
             (forall i :: 0 <= i < |parts[2]| ==> '0' <= parts[2][i] <= '9') &&
             |parts[0]| > 0 && |parts[1]| > 0 && |parts[2]| > 0

lemma ValidInputFromString(s: string)
    requires |s| > 0
    requires var trimmed := if |s| > 0 && s[|s|-1] == '\n' then s[..|s|-1] else s;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3
    requires var trimmed := if |s| > 0 && s[|s|-1] == '\n' then s[..|s|-1] else s;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3 ==>
             (forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9') &&
             (forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9') &&
             (forall i :: 0 <= i < |parts[2]| ==> '0' <= parts[2][i] <= '9') &&
             |parts[0]| > 0 && |parts[1]| > 0 && |parts[2]| > 0
    ensures var trimmed := if |s| > 0 && s[|s|-1] == '\n' then s[..|s|-1] else s;
            var parts := SplitOnSpaces(trimmed);
            |parts| == 3 ==>
            ValidInput(StringToInt(parts[0]), StringToInt(parts[1]), StringToInt(parts[2]))
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3 ==>
             (forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9') &&
             (forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9') &&
             (forall i :: 0 <= i < |parts[2]| ==> '0' <= parts[2][i] <= '9') &&
             |parts[0]| > 0 && |parts[1]| > 0 && |parts[2]| > 0
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3 ==>
             ValidInput(StringToInt(parts[0]), StringToInt(parts[1]), StringToInt(parts[2]))
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
            var parts := SplitOnSpaces(trimmed);
            var a := StringToInt(parts[0]);
            var b := StringToInt(parts[1]);
            var c := StringToInt(parts[2]);
            result == IntToString(RemainingWater(a, b, c)) + "\n"
// </vc-spec>
// <vc-code>
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var parts := SplitOnSpaces(trimmed);
    
    assert |parts| == 3;
    
    var a_str := parts[0];
    var b_str := parts[1];
    var c_str := parts[2];
    
    assert |a_str| > 0 && (forall i :: 0 <= i < |a_str| ==> '0' <= a_str[i] <= '9');
    assert |b_str| > 0 && (forall i :: 0 <= i < |b_str| ==> '0' <= b_str[i] <= '9');
    assert |c_str| > 0 && (forall i :: 0 <= i < |c_str| ==> '0' <= c_str[i] <= '9');
    
    var a := StringToInt(a_str);
    var b := StringToInt(b_str);
    var c := StringToInt(c_str);
    
    assert ValidInput(a, b, c);
    
    var availableSpace := a - b;
    var remaining := c - availableSpace;
    var resultWater := if remaining >= 0 then remaining else 0;
    
    result := IntToString(resultWater) + "\n";
    
    assert |result| > 0;
    assert result[|result|-1] == '\n';
    assert result == IntToString(RemainingWater(a, b, c)) + "\n";
}
// </vc-code>

