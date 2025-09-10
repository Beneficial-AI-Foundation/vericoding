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

// <vc-helpers>
lemma StringToIntHelperNonNeg(s: string)
    ensures StringToIntHelper(s) >= 0
    decreases |s|
{
    if |s| > 0 {
        StringToIntHelperNonNeg(s[..|s|-1]);
    }
}

lemma StringToIntPositive(s: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToInt(s) >= 0
{
    if s[0] == '-' {
        StringToIntHelperNonNeg(s[1..]);
    } else {
        StringToIntHelperNonNeg(s);
    }
}

lemma IntToStringHelperPositive(n: int)
    requires n >= 0
    ensures |IntToStringHelper(n)| > 0 || n == 0
    decreases n
{
    if n > 0 {
        IntToStringHelperPositive(n / 10);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures result == ExpectedOutput(stdin_input)
// </vc-spec>
// <vc-code>
{
  var lines := SplitLinesFunc(stdin_input);
  if |lines| >= 1 {
    var n_str := lines[0];
    var n := StringToInt(n_str);
    if n == 1 {
      result := "Hello World\n";
    } else if |lines| >= 3 {
      var a_str := lines[1];
      var b_str := lines[2];
      var a := StringToInt(a_str);
      var b := StringToInt(b_str);
      var sum := a + b;
      result := IntToString(sum) + "\n";
    } else {
      result := "";
    }
  } else {
    result := "";
  }
}
// </vc-code>

