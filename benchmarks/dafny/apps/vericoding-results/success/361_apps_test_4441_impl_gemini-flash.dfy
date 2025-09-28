// <vc-preamble>
predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0
}

function ExpectedOutput(stdin_input: string): string
{
    var lines := SplitLinesFunc(stdin_input);
    if |lines| >= 1 then
        var n := StringToInt(lines[0]);
        if n == 1 then "Hello World\n"
        else if n != 1 && |lines| >= 3 then
            var a := StringToInt(lines[1]);
            var b := StringToInt(lines[2]);
            IntToString(a + b) + "\n"
        else ""
    else ""
}

function SplitLinesFunc(s: string): seq<string>
{
    SplitLinesFuncHelper(s, 0, "", [])
}

function SplitLinesFuncHelper(s: string, i: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if current == "" then acc else acc + [current]
    else if s[i] == '\n' then
        SplitLinesFuncHelper(s, i + 1, "", acc + [current])
    else
        SplitLinesFuncHelper(s, i + 1, current + [s[i]], acc)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -StringToIntHelper(s[1..])
    else StringToIntHelper(s)
}

function StringToIntHelper(s: string): int
{
    if |s| == 0 then 0
    else StringToIntHelper(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [(n % 10 + '0' as int) as char]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added precondition `|lines| >= 1` to GetN, `|lines| >= 2` to GetA, and `|lines| >= 3` to GetB to resolve index out of range errors */
function {:opaque} GetN(lines: seq<string>): int
    requires |lines| >= 1
{
    StringToInt(lines[0])
}

function {:opaque} GetA(lines: seq<string>): int
    requires |lines| >= 2
{
    StringToInt(lines[1])
}

function {:opaque} GetB(lines: seq<string>): int
    requires |lines| >= 3
{
    StringToInt(lines[2])
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures result == ExpectedOutput(stdin_input)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): The issue in iteration 3 was that ExpectedOutput does not call helper functions, so the postcondition of the method was not aware of the preconditions of the helper functions. Explicitly calling StringToInt on `lines[0]`, `lines[1]` and `lines[2]` resolves this inconsistency, making the method's logic consistent with `ExpectedOutput`. */
{
  var lines := SplitLinesFunc(stdin_input);
  if |lines| >= 1 {
    var n := StringToInt(lines[0]);
    if n == 1 {
      result := "Hello World\n";
    } else if |lines| >= 3 {
      var a := StringToInt(lines[1]);
      var b := StringToInt(lines[2]);
      result := IntToString(a + b) + "\n";
    } else {
      result := "";
    }
  } else {
    result := "";
  }
}
// </vc-code>
