function valid_input_format(input: string): bool
{
    true // Simplified implementation
}

function is_binary_string(s: string): bool
{
    forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

function count_test_cases(input: string): nat
    requires valid_input_format(input)
{
    1 // Simplified implementation
}

function count_lines(s: string): nat
{
    1 // Simplified implementation
}

function get_line(s: string, i: nat): string
    requires i < count_lines(s)
{
    "1" // Simplified implementation
}

function get_string_count(input: string, test_case: nat): nat
    requires test_case < count_test_cases(input)
    requires valid_input_format(input)
{
    1 // Simplified implementation
}

function get_test_case_strings(input: string, test_case: nat): seq<string>
    requires test_case < count_test_cases(input)
    requires valid_input_format(input)
    ensures forall s :: s in get_test_case_strings(input, test_case) ==> is_binary_string(s)
{
    ["0"] // Simplified implementation
}

function string_to_int(s: string): int
{
    1 // Simplified implementation
}

function compute_max_palindromes(strings: seq<string>): nat
    requires forall s :: s in strings ==> is_binary_string(s)
    ensures compute_max_palindromes(strings) <= |strings|
    ensures compute_max_palindromes(strings) == greedy_palindrome_count(strings)
{
    greedy_palindrome_count(strings)
}

function palindromic_strings_achievable(strings: seq<string>, k: nat): bool
    requires forall s :: s in strings ==> is_binary_string(s)
    requires k <= |strings|
{
    k <= greedy_palindrome_count(strings)
}

// <vc-helpers>
function reverse_string(s: string): string
{
  if |s| == 0 then
    ""
  else
    reverse_string(s[0..|s|-1]) + [s[|s|-1]]
}

function is_palindrome_string(s: string): bool
{
  s == reverse_string(s)
}

function greedy_palindrome_count(strings: seq<string>): nat
  requires forall s :: s in strings ==> is_binary_string(s)
{
  var unique_strings: seq<string> = [];
  var seen: set<string> = {};
  for s in strings {
    if s !in seen {
      unique_strings := unique_strings + [s];
      seen := seen + {s};
    }
  }
  var counts: map<string, nat> = map[];
  for s in strings {
    counts := counts[s := (if s in counts then counts[s] else 0) + 1];
  }
  var total: nat = 0;
  var processed: set<string> = {};
  for s in unique_strings {
    if s in processed || !(s == reverse_string(s)) continue;
    if s == reverse_string(s) {
      total := total + counts[s];
      processed := processed + {s};
    } else {
      var r := reverse_string(s);
      var cnt_s := counts[s];
      var cnt_r := if r in counts then counts[r] else 0;
      total := total + min(cnt_s, cnt_r);
      processed := processed + {s, r};
    }
  }
  total
}

function int_to_string(n: nat): string
{
  if n == 0 then
    "0"
  else
    recur(n)
}

ghost method recur(n: nat): string
  requires n > 0
{
  if n < 10 then
    [48 as char + (n as nat)]
  else
    recur(n / 10) + [48 as char + (n % 10)]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires input[|input|-1] == '\n'
    requires valid_input_format(input)
    ensures |result| >= 0
    ensures result == "" || result[|result|-1] == '\n'
    ensures count_lines(result) == count_test_cases(input)
    ensures forall i :: 0 <= i < count_test_cases(input) ==> 
        string_to_int(get_line(result, i)) >= 0
    ensures forall i :: 0 <= i < count_test_cases(input) ==> 
        string_to_int(get_line(result, i)) <= get_string_count(input, i)
    ensures forall i :: 0 <= i < count_test_cases(input) ==> 
        string_to_int(get_line(result, i)) == compute_max_palindromes(get_test_case_strings(input, i))
    ensures forall i :: 0 <= i < count_test_cases(input) ==> 
        palindromic_strings_achievable(get_test_case_strings(input, i), string_to_int(get_line(result, i)))
// </vc-spec>
// <vc-code>
{
  var result: string := "";
  var i: nat := 0;
  while i < count_test_cases(input) {
    var strings := get_test_case_strings(input, i);
    var max_p := greedy_palindrome_count(strings);
    var line := int_to_string(max_p);
    result := result + line + "\n";
    i := i + 1;
  }
  result
}
// </vc-code>

