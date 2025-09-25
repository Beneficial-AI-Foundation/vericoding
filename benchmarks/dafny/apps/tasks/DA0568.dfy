// <vc-preamble>
predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 2 &&
    (var n := StringToInt(lines[0]);
     var parts := SplitBySpace(lines[1]);
     |parts| >= 2 &&
     n >= 0 &&
     n <= |parts[0]| && n <= |parts[1]|)
}

function GetN(input: string): int
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    StringToInt(lines[0])
}

function GetS(input: string): string
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var parts := SplitBySpace(lines[1]);
    parts[0]
}

function GetT(input: string): string
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var parts := SplitBySpace(lines[1]);
    parts[1]
}

function AlternateChars(s: string, t: string, n: int): string
    requires n >= 0
    requires n <= |s| && n <= |t|
    ensures |AlternateChars(s, t, n)| == 2 * n
    ensures forall i :: 0 <= i < n ==> 
        i * 2 < |AlternateChars(s, t, n)| && 
        i * 2 + 1 < |AlternateChars(s, t, n)| &&
        AlternateChars(s, t, n)[i * 2] == s[i] && 
        AlternateChars(s, t, n)[i * 2 + 1] == t[i]
{
    if n == 0 then ""
    else [s[0]] + [t[0]] + AlternateChars(s[1..], t[1..], n - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures ValidInput(input) ==> 
        (var n := GetN(input);
         var s := GetS(input);
         var t := GetT(input);
         |result| == 2 * n + 1 &&
         result[|result| - 1] == '\n' &&
         result[0..|result|-1] == AlternateChars(s, t, n))
    ensures !ValidInput(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
