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
  while i < |s|
    invariant 0 <= i <= |s|
    invariant x >= 0
    invariant forall k :: 0 <= k < i && (s[k] == '-' ==> k == 0) ==> '0' <= s[k] <= '9'
    invariant (i == 0 || (i == 1 && s[0] == '-')) ==> x == 0
    invariant i > 0 && !(i == 1 && s[0] == '-') ==> x == (ParseInt(s[ (if s[0] == '-' then 1 else 0)..i]) / sign)
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
  ensures |s| == 0 ==> |SplitLines(s)| == 1 && SplitLines(s)[0] == ""
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
  ensures |s| == 0 ==> |SplitSpaces(s)| == 0
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
  if t < 0 { // Handle negative t gracefully, assuming it means 0 test cases
      t := 0;
  }

  for i := 1 to t
    invariant 1 <= i <= t + 1
    invariant resultBuilder.Length >= 0
    invariant forall k :: 0 <= k < resultBuilder.Length ==> resultBuilder.ToString()[k] in "YNesNo\n "
    // This invariant ensures that the output built so far matches the expected output
    // for all test cases from 1 up to i-1.
    invariant forall j :: 1 <= j < i ==>
      var current_line_content := if j < |lines| then lines[j] else "";
      var parts := SplitSpaces(current_line_content);
      var expectedOutputSegment := "";
      if |parts| >= 3 {
        var n_str := parts[0];
        var l_str := parts[1];
        var r_str := parts[2];
        // Ensure parsing is safe for the invariant
        if |n_str| > 0 && |l_str| > 0 && |r_str| > 0 &&
           (forall c :: c in n_str ==> '0' <= c <= '9' || c == '-') &&
           (forall c :: c in l_str ==> '0' <= c <= '9' || c == '-') &&
           (forall c :: c in r_str ==> '0' <= c <= '9' || c == '-')
        {
          var n := ParseInt(n_str);
          var l := ParseInt(l_str);
          var r := ParseInt(r_str);
          expectedOutputSegment := if CanMakeSum(n, l, r) then "Yes" else "No";
        } else {
             // If parsing fails for any part, assume default "No" to avoid invalid integer issues in spec
            expectedOutputSegment := "No";
        }
      } else {
        expectedOutputSegment := "No"; // If parts are missing, assume "No"
      }
      var totalPrefLen := 0;
      for k := 1 to j-1 {
        var prev_line_content := if k < |lines| then lines[k] else "";
        var prev_parts := SplitSpaces(prev_line_content);
        var prev_expected_output_segment := "";

        if |prev_parts| >= 3 {
            var prev_n_str := prev_parts[0];
            var prev_l_str := prev_parts[1];
            var prev_r_str := prev_parts[2];
            if |prev_n_str| > 0 && |prev_l_str| > 0 && |prev_r_str| > 0 &&
               (forall c :: c in prev_n_str ==> '0' <= c <= '9' || c == '-') &&
               (forall c :: c in prev_l_str ==> '0' <= c <= '9' || c == '-') &&
               (forall c :: c in prev_r_str ==> '0' <= c <= '9' || c == '-')
            {
                var prev_n := ParseInt(prev_n_str);
                var prev_l := ParseInt(prev_l_str);
                var prev_r := ParseInt(prev_r_str);
                prev_expected_output_segment := if CanMakeSum(prev_n, prev_l, prev_r) then "Yes" else "No";
            } else {
                 prev_expected_output_segment := "No";
            }
        } else {
            prev_expected_output_segment := "No";
        }
        totalPrefLen := totalPrefLen + |prev_expected_output_segment| + 1; // +1 for the newline
      }
      totalPrefLen + |expectedOutputSegment| + 1 <= resultBuilder.Length &&
      resultBuilder.ToString()[totalPrefLen .. totalPrefLen + |expectedOutputSegment|] == expectedOutputSegment
  {
    if i < |lines|
    {
      var parts := SplitSpaces(lines[i]);
      if |parts| >= 3 {
        var n_str := parts[0];
        var l_str := parts[1];
        var r_str := parts[2];
        var res := "No"; // Default to No

        // Add checks for valid integer strings before parsing
        if |n_str| > 0 && (forall c :: c in n_str ==> '0' <= c <= '9' || c == '-') &&
           |l_str| > 0 && (forall c :: c in l_str ==> '0' <= c <= '9' || c == '-') &&
           |r_str| > 0 && (forall c :: c in r_str ==> '0' <= c <= '9' || c == '-')
        {
            var n := ParseInt(n_str);
            var l := ParseInt(l_str);
            var r := ParseInt(r_str);
            res := if CanMakeSum(n, l, r) then "Yes" else "No";
        }
        resultBuilder.Append(res);
      } else {
        resultBuilder.Append("No"); // If parts are missing as per spec
      }
      resultBuilder.Append("\n");
    } else {
      // If i >= |lines|, we still need to append a "No" and a newline for each remaining test case up to 't'.
      // This is because the problem statement implies T test cases are processed,
      // and if input lines are fewer than T, the remaining ones are processed with default values,
      // or in this case, simply result in a newline in the output.
      resultBuilder.Append("No"); // As per spec, if parameters are missing, output "No"
      resultBuilder.Append("\n");
    }
  }

  result := resultBuilder.ToString();
  return result;
}
// </vc-code>

