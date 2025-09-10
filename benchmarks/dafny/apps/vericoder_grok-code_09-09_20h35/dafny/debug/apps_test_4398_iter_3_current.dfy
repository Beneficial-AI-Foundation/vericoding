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
function IndexOf(s: string, c: char, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start == |s| then -1
    else if s[start] == c then start
    else IndexOf(s, c, start + 1)
}

function Split(s: string, delim: char): seq<string>
    decreases |s|
{
    var idx := IndexOf(s, delim, 0);
    if idx == -1 then [s]
    else if idx == 0 then [""] + Split(s[1..], delim)
    else [s[0..idx]] + Split(s[idx+1..], delim)
}

function SplitLines(input: string): seq<string>
    decreases |input|
{
    Split(input, '\n')
}

function SplitBySpace(s: string): seq<string>
    decreases |s|
{
    Split(s, ' ')
}

function StringToInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 0 then 0
    else 10 * StringToInt(s[0..|s|-1]) + ((s[|s|-1] as int) - ('0' as int))
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
  var lines := SplitLines(input);
  if (|lines| < 2) {
    return "";
  }
  var line0 := lines[0];
  var allDigits := true;
  var i := 0;
  while i < |line0|
  {
    if (!('0' <= line0[i] <= '9')) {
      allDigits := false;
      break;
    }
    i := i + 1;
  }
  if (!allDigits) {
    return "";
  }
  var n := StringToInt(line0);
  var parts := SplitBySpace(lines[1]);
  if (|parts| < 2) {
    return "";
  }
  var s := parts[0];
  var t := parts[1];
  if (n < 0 || n > |s| || n > |t|) {
    return "";
  }
  var alt := AlternateChars(s, t, n);
  return alt + "\n";
}
// </vc-code>

