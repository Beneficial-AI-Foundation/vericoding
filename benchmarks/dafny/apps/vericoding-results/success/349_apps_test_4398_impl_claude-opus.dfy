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

// <vc-helpers>
// Helper function to split a string by newlines
function SplitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else if '\n' in s then
        var idx := FindNewline(s);
        [s[..idx]] + SplitLines(s[idx+1..])
    else [s]
}

// Helper function to find the first newline in a string
function FindNewline(s: string): nat
    requires '\n' in s
    ensures 0 <= FindNewline(s) < |s|
    ensures s[FindNewline(s)] == '\n'
    ensures forall i :: 0 <= i < FindNewline(s) ==> s[i] != '\n'
{
    if s[0] == '\n' then 0
    else 1 + FindNewline(s[1..])
}

// Helper function to split a string by spaces
function SplitBySpace(s: string): seq<string>
{
    if |s| == 0 then []
    else if ' ' in s then
        var idx := FindSpace(s);
        [s[..idx]] + SplitBySpace(s[idx+1..])
    else [s]
}

// Helper function to find the first space in a string
function FindSpace(s: string): nat
    requires ' ' in s
    ensures 0 <= FindSpace(s) < |s|
    ensures s[FindSpace(s)] == ' '
    ensures forall i :: 0 <= i < FindSpace(s) ==> s[i] != ' '
{
    if s[0] == ' ' then 0
    else 1 + FindSpace(s[1..])
}

// Helper function to convert string to integer
function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then CharToDigit(s[0])
    else StringToInt(s[..|s|-1]) * 10 + CharToDigit(s[|s|-1])
}

// Helper function to convert a character to its digit value
function CharToDigit(c: char): int
{
    if '0' <= c <= '9' then (c as int) - ('0' as int)
    else 0
}

// Helper lemmas for AlternateChars if needed
lemma AlternateCharsLength(s: string, t: string, n: int)
    requires n >= 0
    requires n <= |s| && n <= |t|
    ensures |AlternateChars(s, t, n)| == 2 * n
{
    // This follows directly from the ensures clause of AlternateChars
}
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
    if !ValidInput(input) {
        return "";
    }
    
    var n := GetN(input);
    var s := GetS(input);
    var t := GetT(input);
    
    var alternated := AlternateChars(s, t, n);
    result := alternated + "\n";
}
// </vc-code>

