predicate ValidInput(input: string)
{
    |input| > 0
}

function CanMakeSum(n: int, l: int, r: int): bool
{
    l > 0 && l <= r && n > 0 && n % l <= (r - l) * (n / l)
}

predicate ValidOutput(result: string)
{
    |result| >= 0 && forall i :: 0 <= i < |result| ==> result[i] in "Yes\nNo\n "
}

predicate CorrectSolution(input: string, result: string)
{
    var lines := SplitLines(input);
    |lines| > 0 ==> 
    (var t := ParseInt(lines[0]);
     var outputLines := SplitLines(result);
     |outputLines| >= 1 && (|outputLines| == 1 ==> outputLines[0] == "") &&
     (|outputLines| > 1 ==> outputLines[|outputLines|-1] == "") &&
     forall i :: 1 <= i <= t && i < |lines| ==>
        (var parts := SplitSpaces(lines[i]);
         |parts| >= 3 ==>
         (var n := ParseInt(parts[0]);
          var l := ParseInt(parts[1]);
          var r := ParseInt(parts[2]);
          var expectedOutput := if CanMakeSum(n, l, r) then "Yes" else "No";
          i-1 < |outputLines| && outputLines[i-1] == expectedOutput)))
}

// <vc-helpers>
function ParseInt(s: string): int
  reads s
{
  var x := 0;
  var i := 0;
  var sign := 1;
  if |s| > 0 && s[0] == '-' then
    sign := -1;
    i := 1;
  else
    skip;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant x >= 0
    invariant forall k :: 0 <= k < i && (s[k] == '-' ==> k == 0) ==> '0' <= s[k] <= '9'
  {
    assert '0' <= s[i] <= '9';
    x := x * 10 + (s[i] - '0');
    i := i + 1;
  }
  return sign * x;
}

function SplitLines(s: string): seq<string>
  reads s
  ensures forall i :: 0 <= i < |SplitLines(s)| ==> forall c :: c in SplitLines(s)[i] ==> c != '\n'
  ensures forall i :: 0 <= i < |SplitLines(s)| && i < |SplitLines(s)| - 1 ==> SplitLines(s)[i] != "" || |s| == 0
{
  var lines: seq<string> := [];
  var start := 0;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant 0 <= start <= i
    invariant forall k :: 0 <= k < |lines| ==> forall c :: c in lines[k] ==> c != '\n'
    invariant forall k :: 0 <= k < |lines| && k < |lines| -1 ==> lines[k] != "" || |s| == 0
  {
    if i == |s| || s[i] == '\n' {
      lines := lines + [s[start..i]];
      start := i + 1;
    }
  }
  return lines;
}

function SplitSpaces(s: string): seq<string>
  reads s
  ensures forall i :: 0 <= i < |SplitSpaces(s)| ==> forall c :: c in SplitSpaces(s)[i] ==> c != ' '
{
  var parts: seq<string> := [];
  var start := 0;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant 0 <= start <= i
    invariant forall k :: 0 <= k < |parts| ==> forall c :: c in parts[k] ==> c != ' '
  {
    if i == |s| || s[i] == ' ' {
      if start < i {
        parts := parts + [s[start..i]];
      }
      start := i + 1;
    }
  }
  return parts;
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures CorrectSolution(input, result)
// </vc-spec>
// <vc-code>
{
  var lines := SplitLines(input);
  var resultBuilder := new System.Text.StringBuilder();

  if |lines| == 0 {
    return "";
  }

  var t := ParseInt(lines[0]);
  for i := 1 to t
    invariant 1 <= i <= t + 1
    invariant resultBuilder.Length >= 0
    invariant forall k :: 0 <= k < resultBuilder.Length ==> resultBuilder[k] in "YNesNo\n "
    // The loop invariant below ensures that the parts of resultBuilder match the expected output
    // for all processed test cases.
    invariant forall j :: 1 <= j < i && j < |lines| ==>
      var parts := SplitSpaces(lines[j]);
      (
        |parts| >= 3 &&
        var n := ParseInt(parts[0]);
        var l := ParseInt(parts[1]);
        var r := ParseInt(parts[2]);
        var expectedOutput := if CanMakeSum(n, l, r) then "Yes" else "No";
        var start_idx := 0;
        var end_idx := 0;
        match j {
          case 1 => start_idx := 0;
          case _ =>
            var prev_expected_output_len := 0;
            for k := 1 to j-1 {
              var prev_parts := SplitSpaces(lines[k]);
              if |prev_parts| >= 3 {
                var prev_n := ParseInt(prev_parts[0]);
                var prev_l := ParseInt(prev_parts[1]);
                var prev_r := ParseInt(prev_parts[2]);
                prev_expected_output_len := prev_expected_output_len + |(if CanMakeSum(prev_n, prev_l, prev_r) then "Yes" else "No")| + 1; // +1 for the newline
              } else {
                prev_expected_output_len := prev_expected_output_len + 1; // For cases where parts < 3, an empty string is added for output + newline
              }
            }
            start_idx := prev_expected_output_len;
        }
        end_idx := start_idx + |expectedOutput|;
        start_idx >= 0 && end_idx <= resultBuilder.Length &&
        resultBuilder.ToString()[start_idx..end_idx] == expectedOutput
      )
  {
    if i < |lines|
    {
      var parts := SplitSpaces(lines[i]);
      if |parts| >= 3 {
        var n := ParseInt(parts[0]);
        var l := ParseInt(parts[1]);
        var r := ParseInt(parts[2]);
        var res := if CanMakeSum(n, l, r) then "Yes" else "No";
        resultBuilder.Append(res);
      }
      resultBuilder.Append("\n");
    } else {
      // If i >= |lines|, we still need to append a newline for each remaining test case up to 't'.
      // This is because the problem statement implies T test cases are processed,
      // and if input lines are fewer than T, the remaining ones are processed with default values,
      // or in this case, simply result in a newline in the output.
      resultBuilder.Append("\n");
    }
  }

  result := resultBuilder.ToString();
  return result;
}
// </vc-code>

