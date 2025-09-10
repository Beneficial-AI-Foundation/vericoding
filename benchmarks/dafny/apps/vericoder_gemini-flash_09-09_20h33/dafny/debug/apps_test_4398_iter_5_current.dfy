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
function SplitLines(input: string): seq<string>
  ensures forall i :: 0 <= i < |SplitLines(input)| ==> |SplitLines(input)[i]| > 0
{
  if input == "" then
    []
  else if input contains '\n' then
    var idx := input.IndexOf('\n');
    [input[0..idx]] + SplitLines(input[idx + 1 ..])
  else
    [input]
}

function StringToInt(s: string): int
  // Added requires clause to ensure string contains only digits or is empty
  requires forall c :: c in s ==> '0' <= c <= '9'
  // Added ensures clause to guarantee non-negative return value
  ensures StringToInt(s) >= 0 // Ensure non-negative for typical usage
{
  if s == "" then 0 else s as int
}

function SplitBySpace(input: string): seq<string>
  ensures forall i :: 0 <= i < |SplitBySpace(input)| ==> |SplitBySpace(input)[i]| > 0
{
  if input == "" then
    []
  else if input contains ' ' then
    var idx := input.IndexOf(' ');
    // Handle cases where the space is at the beginning or there are multiple spaces
    var head := input[0..idx];
    var tail := input[idx + 1 ..];
    (if head == "" then [] else [head]) + SplitBySpace(tail)
  else
    [input]
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
    if ValidInput(input) then
        var n := GetN(input);
        var s := GetS(input);
        var t := GetT(input);
        var res := AlternateChars(s, t, n);
        return res + "\n";
    else
        return "";
    
}
// </vc-code>

