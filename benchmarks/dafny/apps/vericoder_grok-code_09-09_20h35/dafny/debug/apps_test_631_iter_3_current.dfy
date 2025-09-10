predicate valid_input_format(s: string)
{
    |s| >= 7 && 
    exists pos :: 0 < pos < |s| && s[pos] == '\n'
}

function get_test_count(stdin_input: string): int
    requires valid_input_format(stdin_input)
    ensures get_test_count(stdin_input) >= 1
{
    1
}

function get_array_sum(stdin_input: string, test_idx: int): int
    requires valid_input_format(stdin_input)
    requires 0 <= test_idx < get_test_count(stdin_input)
{
    0
}

function get_target_m(stdin_input: string, test_idx: int): int
    requires valid_input_format(stdin_input)
    requires 0 <= test_idx < get_test_count(stdin_input)
{
    0
}

function expected_output_for_input(stdin_input: string): string
    requires valid_input_format(stdin_input)
{
    compute_expected_output(stdin_input, 0, get_test_count(stdin_input))
}

predicate behavioral_correctness(stdin_input: string, result: string)
    requires valid_input_format(stdin_input)
{
    var T := get_test_count(stdin_input);
    count_responses(result) == T &&
    (forall i :: 0 <= i < T ==>
        var array_sum := get_array_sum(stdin_input, i);
        var target_m := get_target_m(stdin_input, i);
        var response := get_response_at_index(result, i);
        (array_sum == target_m <==> response == "YES\n") &&
        (array_sum != target_m <==> response == "NO\n"))
}

// <vc-helpers>
function parse_int(s: string, start: nat, end: nat): nat
requires start <= end <= |s|
requires forall i: nat :: start <= i < end ==> '0' <= s[i] <= '9'
{
 if start == end then 0 else 
  10 * parse_int(s, start, end-1) + (s[end-1] as int - '0' as int)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires valid_input_format(stdin_input)
    requires |stdin_input| > 0
    requires stdin_input != ""
    requires '\n' in stdin_input
    requires exists pos :: 0 <= pos < |stdin_input| && stdin_input[pos] == '\n'
    requires forall i :: 0 <= i < |stdin_input| ==> 
        stdin_input[i] in
// </vc-spec>
// <vc-code>
{
  var result := "";
  var pos := 0;
  var T := 0;
  while pos < |stdin_input| && stdin_input[pos] != '\n' {
    T := T * 10 + (stdin_input[pos] as int - '0' as int);
    pos := pos + 1;
  }
  pos := pos + 1;
  for t := 0 to T-1 {
    var N := 0;
    while pos < |stdin_input| && stdin_input[pos] != ' ' {
      N := N * 10 + (stdin_input[pos] as int - '0' as int);
      pos := pos + 1;
    }
    pos := pos + 1;
    var M := 0;
    while pos < |stdin_input| && stdin_input[pos] != '\n' {
      M := M * 10 + (stdin_input[pos] as int - '0' as int);
      pos := pos + 1;
    }
    pos := pos + 1;
    var sum := 0;
    for i := 0 to N-1 {
      var num := 0;
      while pos < |stdin_input| && stdin_input[pos] != ' ' && stdin_input[pos] != '\n' {
        num := num * 10 + (stdin_input[pos] as int - '0' as int);
        pos := pos + 1;
      }
      if pos < |stdin_input| { pos := pos + 1; }
      sum := sum + num;
    }
    if sum == M {
      result := result + "YES\n";
    } else {
      result := result + "NO\n";
    }
  }
}
// </vc-code>

