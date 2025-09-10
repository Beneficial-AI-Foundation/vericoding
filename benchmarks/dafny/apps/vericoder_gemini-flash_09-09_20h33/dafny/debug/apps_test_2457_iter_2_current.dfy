predicate ValidInput(input: string) {
    |input| >= 0
}

predicate ValidTestCase(n: int, a: int, b: int, c: int, d: int) {
    n >= 1 && n <= 1000 &&
    a >= 0 && a <= 1000 &&
    b >= 0 && b < a &&
    c >= 0 && c <= 1000 &&
    d >= 0 && d < c
}

function CanAchieveWeight(n: int, a: int, b: int, c: int, d: int): bool {
    var minWeight := (a - b) * n;
    var maxWeight := (a + b) * n;
    var targetMin := c - d;
    var targetMax := c + d;
    !(minWeight > targetMax || maxWeight < targetMin)
}

predicate ValidOutput(output: string) {
    forall i :: 0 <= i < |output| ==> output[i] in "YesNo\n"
}

// <vc-helpers>
function CountNewlines(s: string): int
{
  if s == "" then 0
  else (if s[0] == '\n' then 1 else 0) + CountNewlines(s[1..])
}

function StripTrailingNewlines(s: string): string
{
  var i := |s|;
  while i > 0 && s[i-1] == '\n'
    decreases i
  {
    i := i - 1;
  }
  return s[0..i];
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures (input == "" || input == "\n") ==> result == ""
    ensures input != "" && input != "\n" ==> (|result| > 0 ==> result[|result|-1] == '\n' || (|result| > 3 && result[|result|-4..] in ["Yes\n", "No\n"]))
// </vc-spec>
// <vc-code>
{
    var lines := input.Split('\n');
    var numTestCases := 0;
    if |lines| > 0 && lines[0] != "" {
        numTestCases := Std.ParseInt(lines[0]);
    }

    var outputLines := new array<string>(numTestCases);
    var currentLine := 1;

    forall i | 0 <= i < numTestCases
        ensures (CanAchieveWeight(Std.ParseInt(lines[currentLine + i * 2]), Std.ParseInt(lines[currentLine + i * 2 + 1].Split(' ')[0]), Std.ParseInt(lines[currentLine + i * 2 + 1].Split(' ')[1]), Std.ParseInt(lines[currentLine + i * 2 + 1].Split(' ')[2]), Std.ParseInt(lines[currentLine + i * 2 + 1].Split(' ')[3]))) ==> outputLines[i] == "Yes"
        ensures (!CanAchieveWeight(Std.ParseInt(lines[currentLine + i * 2]), Std.ParseInt(lines[currentLine + i * 2 + 1].Split(' ')[0]), Std.ParseInt(lines[currentLine + i * 2 + 1].Split(' ')[1]), Std.ParseInt(lines[currentLine + i * 2 + 1].Split(' ')[2]), Std.ParseInt(lines[currentLine + i * 2 + 1].Split(' ')[3]))) ==> outputLines[i] == "No"
    {
        var n := Std.ParseInt(lines[currentLine + i * 2]);
        var parts := lines[currentLine + i * 2 + 1].Split(' ');
        var a := Std.ParseInt(parts[0]);
        var b := Std.ParseInt(parts[1]);
        var c := Std.ParseInt(parts[2]);
        var d := Std.ParseInt(parts[3]);

        if CanAchieveWeight(n, a, b, c, d) {
            outputLines[i] := "Yes";
        } else {
            outputLines[i] := "No";
        }
    }

    result := "";
    for i := 0 to numTestCases - 1
        invariant 0 <= i <= numTestCases
        invariant forall k :: 0 <= k < i ==> (outputLines[k] == "Yes" || outputLines[k] == "No")
        invariant result == (if i == 0 then "" else Std.Join(outputLines[0..i-1], "\n") + "\n")
    {
        result := result + outputLines[i] + "\n";
    }

    // Handle the case where input is empty or just newlines
    if input == "" || StripTrailingNewlines(input) == "" {
        result := "";
    } else if |result| > 0 && result[|result|-1] == '\n' && CountNewlines(StripTrailingNewlines(input)) < {|lines|} -1 {
        // If the original input didn't end with a newline, or had fewer newlines than lines implies,
        // and our result ends with one, strip the last generated newline.
        // This is a heuristic to match typical competitive programming output format.
        result := result[0..|result|-1];
    }
}
// </vc-code>

