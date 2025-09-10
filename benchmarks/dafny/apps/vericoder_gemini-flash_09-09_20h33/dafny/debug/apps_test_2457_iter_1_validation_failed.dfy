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
import "StandardLibrary/Char.dfy"
import "StandardLibrary/Strings.dfy"

lemma BytesUntilChar(s: string, start: int, c: char) returns (index: int)
  requires 0 <= start <= |s|
  ensures
    if exists i :: start <= i < |s| && s[i] == c then
      start <= index < |s| && s[index] == c &&
      forall k :: start <= k < index ==> s[k] != c
    else
      index == |s|
{
  var i := start;
  while i < |s|
    invariant start <= i <= |s|
    invariant forall k :: start <= k < i ==> s[k] != c
  {
    if s[i] == c {
      return i;
    }
    i := i + 1;
  }
  return |s|;
}

function StrToInt(s: string): (i: int)
  requires (forall c :: c in s ==> c in '0'..'9')
  ensures (s == "" ==> i == 0)
  ensures (s != "" ==> i >= 0)
{
  var n := 0;
  var k := 0;
  while k < |s|
    invariant 0 <= k <= |s|
    invariant n >= 0
    invariant n == (if k == 0 then 0 else StrToInt(s[..k]))
  {
    n := n * 10 + (s[k] as int - '0' as int);
    k := k + 1;
  }
  return n;
}

lemma method ParseInt(s: string, start: int) returns (value: int, end: int)
  requires 0 <= start <= |s|
  requires (exists k :: start <= k < |s| && '0' <= s[k] <= '9') // At least one digit
  ensures start <= end <= |s|
  ensures forall i :: start <= i < end ==> '0' <= s[i] <= '9'
  ensures (end == |s| || s[end] !in '0'..'9')
  ensures value == StrToInt(s[start..end])
{
  var current := start;
  while current < |s| && '0' <= s[current] <= '9'
    invariant start <= current <= |s|
  {
    current := current + 1;
  }
  end := current;
  value := StrToInt(s[start..end]);
}

lemma method GetNextLine(s: string, start: int) returns (line: string, end: int)
  requires 0 <= start <= |s|
  ensures start <= end <= |s|
  ensures (exists i :: start <= i < |s| && s[i] == '\n') ==> (line == s[start .. BytesUntilChar(s, start, '\n')] && end == BytesUntilChar(s, start, '\n') + 1)
  ensures (forall i :: start <= i < |s| ==> s[i] != '\n') ==> (line == s[start..] && end == |s|)
{
    var next_newline_index := BytesUntilChar(s, start, '\n');
    line := s[start .. next_newline_index];
    if next_newline_index < |s| {
        end := next_newline_index + 1;
    } else {
        end := |s|;
    }
}

lemma method SplitBySpace(s: string) returns (parts: seq<string>)
  ensures forall p :: p in parts ==> forall c :: c in p ==> c != ' '
  ensures |parts| > 0 ==> s == String.Join(" ", parts)
  ensures |parts| == 0 ==> s == ""
{
  parts := [];
  var current_idx := 0;
  while current_idx < |s|
    invariant 0 <= current_idx <= |s|
    invariant (forall p :: p in parts ==> forall c :: c in p ==> c != ' ')
    invariant (String.Join(" ", parts) + (if current_idx > 0 && current_idx < |s| && s[current_idx-1] != ' ' then " " else "") + s[current_idx..] == s)
  {
    var space_idx := BytesUntilChar(s, current_idx, ' ');

    if space_idx > current_idx {
      parts := parts + [s[current_idx..space_idx]];
    }
    
    current_idx := space_idx;
    if current_idx < |s| && s[current_idx] == ' ' {
      current_idx := current_idx + 1; // Move past the space
    }
  }
  // Handle the case where the string is just spaces or ends with spaces
  if |s| > 0 && |parts| == 0 && (forall c :: c in s ==> c == ' ') {
      parts:= [""]; // If it's all spaces, treat as single empty part, or refine requirements
  } else if |s| > 0 && s[|s|-1] == ' ' {
      // If ends with space, there's effectively an empty part after it
      // This is a subtle point, common string splitting might include this
  }
  assert true; // Dummy assert
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
    if input == "" || input == "\n" {
        return "";
    }

    var result_lines: seq<string> := [];
    var current_index := 0;

    // Skip the first line (number of test cases)
    var header_line: string;
    var next_index: int;
    header_line, next_index := GetNextLine(input, current_index);
    current_index := next_index;

    while current_index < |input| {
        var line: string;
        line, next_index := GetNextLine(input, current_index);
        current_index := next_index;

        if line == "" { // Handle empty lines if any (e.g., trailing newline)
             break;
        }

        var parts: seq<string>;
        parts := SplitBySpace(line);

        if |parts| != 5 {
            // Malformed line, skip or handle as error; here we'll just break
            break;
        }

        var n_val: int;
        var a_val: int;
        var b_val: int;
        var c_val: int;
        var d_val: int;

        var temp_end: int;

        n_val, temp_end := ParseInt(parts[0], 0);
        a_val, temp_end := ParseInt(parts[1], 0);
        b_val, temp_end := ParseInt(parts[2], 0);
        c_val, temp_end := ParseInt(parts[3], 0);
        d_val, temp_end := ParseInt(parts[4], 0);

        if ValidTestCase(n_val, a_val, b_val, c_val, d_val) {
            if CanAchieveWeight(n_val, a_val, b_val, c_val, d_val) {
                result_lines := result_lines + ["Yes"];
            } else {
                result_lines := result_lines + ["No"];
            }
        } else {
            // Invalid test case according to predicate. Based on problem constraints,
            // we should assume valid input formats once parsed.
            // If the problem implies that `ValidTestCase` also covers input format validity,
            // then perhaps we should treat it as an error or skip.
            // For now, assume a well-formed input and an invalid test case leads to 'No' or 'Yes' based on `CanAchieveWeight`.
            // However, the `ValidTestCase` predicate is a precondition check for the arguments.
            // If inputs are outside of range, `CanAchieveWeight` might still run.
            // The problem statement implies we produce "Yes" or "No" for each valid test case *as parsed*.
            // Assume we still run CanAchieveWeight for parsed values, even if they don't fully meet `ValidTestCase` beyond basic parsing requirements.
            // But if they don't satisfy `ValidTestCase`, the result might be undefined w.r.t problem statement's intent.
            // Given the original problem context, `ValidTestCase` defines the *domain* of inputs.
            // If the inputs supplied are out of this domain, the behavior is not specified.
            // For robust solution, we might add a default behavior, e.g., "Error" or "No".
            // Here, we just let `CanAchieveWeight` decide.
            if CanAchieveWeight(n_val, a_val, b_val, c_val, d_val) {
                result_lines := result_lines + ["Yes"];
            } else {
                result_lines := result_lines + ["No"];
            }
        }
    }

    result := String.Join("\n", result_lines);
    if |result_lines| > 0 {
      result := result + "\n";
    }
    return result;
}
// </vc-code>

