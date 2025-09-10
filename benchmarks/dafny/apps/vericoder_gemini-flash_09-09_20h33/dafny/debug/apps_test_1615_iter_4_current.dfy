ghost predicate ValidInputFormat(s: string) {
    var lines := SplitLines(s);
    |lines| >= 1 &&
    exists n: nat, k: nat :: 
        ParsesAsIntegers(lines[0], n as int, k as int) && n > 0 && k > 0 && |lines| >= n + 1 &&
        (forall i :: 1 <= i <= n && i < |lines| ==> 
            exists a: int, b: int :: ParsesAsIntegers(lines[i], a, b))
}

ghost predicate ParsedCorrectly(input: string, n: nat, k: nat, segments: seq<(int, int)>) {
    var lines := SplitLines(input);
    |lines| >= n + 1 && |segments| == n &&
    ParsesAsIntegers(lines[0], n as int, k as int) &&
    (forall i :: 0 <= i < n && i + 1 < |lines| ==> 
        ParsesAsIntegers(lines[i + 1], segments[i].0, segments[i].1))
}

predicate IsValidOutput(s: string) {
    |s| > 0 && s[|s| - 1] == '\n' && 
    (forall i :: 0 <= i < |s| - 1 ==> s[i] != '\n') &&
    IsNumericOutput(s[..|s| - 1])
}

function MinMovesToDivisible(segments: seq<(int, int)>, k: nat): nat
    requires k > 0
    ensures MinMovesToDivisible(segments, k) < k
{
    var totalCoverage := TotalCoverage(segments);
    var remainder := totalCoverage % k;
    if remainder == 0 then 0 else k - remainder
}

function TotalCoverage(segments: seq<(int, int)>): nat {
    if |segments| == 0 then 0
    else SegmentLength(segments[0]) + TotalCoverage(segments[1..])
}

function SegmentLength(segment: (int, int)): nat
    ensures SegmentLength(segment) >= 1
{
    var maxVal := MaxInt(segment.0, segment.1);
    var minVal := MinInt(segment.0, segment.1);
    if maxVal >= minVal then (maxVal - minVal + 1) as nat else 1
}

// <vc-helpers>
function MaxInt(a: int, b: int): int {
  if a >= b then a else b
}

function MinInt(a: int, b: int): int {
  if a <= b then a else b
}

function IsDigit(c: char): bool {
  '0' <= c <= '9'
}

function IsNumeric(s: string): bool {
  forall i :: 0 <= i < |s| ==> IsDigit(s[i])
}

function IsNumericOutput(s: string): bool {
    |s| > 0 && IsNumeric(s)
}

function StrToInt(s: string): int
  requires IsNumeric(s)
  reads {}
  ensures StrToInt(s) >= 0 // Assuming non-negative integers
{
  if |s| == 0 then 0
  else (s[0] as int - '0' as int) * (Power(10, |s| - 1)) + StrToInt(s[1..])
}

function Power(base: int, exp: nat): int
  requires base >= 0
  decreases exp
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}


function IntToString(n: int): string
  requires n >= 0
{
  if n == 0 then "0"
  else 
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant (s != "" ==> (temp == 0 || IsNumeric(s)))
      invariant (temp == 0 || s[0] != '0')
    {
      s := (((temp % 10) as char) + '0') + s;
      temp := temp / 10;
    }
    s
}

function SplitLines(s: string): seq<string> {
  var lines: seq<string> := [];
  var start := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= start <= i
    invariant forall j :: 0 <= j < |lines| ==> !ContainsNewline(lines[j])
  {
    if s[i] == '\n' {
      lines := lines + [s[start..i]];
      start := i + 1;
    }
    i := i + 1;
  }
  if start < |s| {
    lines := lines + [s[start..]];
  } else if start == |s| && |s| > 0 && s[|s|-1] == '\n' {
    lines := lines + [""];
  }
  return lines
}

function ContainsNewline(s: string): bool {
  exists i :: 0 <= i < |s| && s[i] == '\n'
}

predicate ParsesAsIntegers(line: string, out a: int, out b: int)
  ensures ParsesAsIntegers(line, a, b) ==> a >= 0 && b >= 0
{
  var parts := SplitBySpace(line);
  (if |parts| == 2 && IsNumeric(parts[0]) && IsNumeric(parts[1])
   then (a := StrToInt(parts[0]); b := StrToInt(parts[1]); true)
   else (a := 0; b := 0; false))
}

function SplitBySpace(s: string): seq<string>
{
  var parts: seq<string> := [];
  var start := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= start <= i
    invariant forall j :: 0 <= j < |parts| ==> !ContainsSpace(parts[j])
  {
    if s[i] == ' ' {
      parts := parts + [s[start..i]];
      start := i + 1;
    }
    i := i + 1;
  }
  parts := parts + [s[start..]];
  return parts
}

function ContainsSpace(s: string): bool {
  exists i :: 0 <= i < |s| && s[i] == ' '
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires stdin_input[|stdin_input| - 1] == '\n' || !ContainsNewline(stdin_input)
    ensures |result| == 0 || result[|result| - 1] == '\n'
    ensures ValidInputFormat(stdin_input) ==> 
        exists n: nat, k: nat, segments: seq<(int, int)> ::
            n > 0 && k > 0 && |segments| == n &&
            ParsedCorrectly(stdin_input, n, k, segments) &&
            result == IntToString(MinMovesToDivisible(segments, k)) + "\n"
    ensures ValidInputFormat(stdin_input) ==> IsValidOutput(result)
    ensures !ValidInputFormat(stdin_input) ==> 
        (result == "" || (|result| > 0 && result[|result| - 1] == '\n'))
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(stdin_input);

    if |lines| < 1 {
      return ""; // Not a valid input format
    }

    var n_val: int := 0;
    var k_val: int := 0;
    if ParsesAsIntegers(lines[0], n_val, k_val) then
    {
      if n_val <= 0 || k_val <= 0 {
        return "";
      }

      if n_val as int + 1 > |lines| {
        return ""; // Not enough lines for all segments
      }

      var segments: seq<(int, int)> := [];
      var i := 0;
      while i < n_val
        invariant 0 <= i <= n_val
        invariant |segments| == i
        invariant forall j :: 0 <= j < |segments| ==> segments[j].0 >= 0 && segments[j].1 >= 0
        invariant forall j :: 0 <= j < i ==> j + 1 < |lines|
      {
        var a_val: int := 0;
        var b_val: int := 0;
        if i + 1 < |lines| && ParsesAsIntegers(lines[i + 1], a_val, b_val) then
        {
          segments := segments + [(a_val, b_val)];
        } else {
          return ""; // Segment line malformed or missing
        }
        i := i + 1;
      }
      if |segments| == n_val {
        // Here, the input is valid and parsed
        var moves := MinMovesToDivisible(segments, k_val as nat);
        return IntToString(moves) + "\n";
      }
    }
    
    return ""; // Fallback for invalid format
}
// </vc-code>

