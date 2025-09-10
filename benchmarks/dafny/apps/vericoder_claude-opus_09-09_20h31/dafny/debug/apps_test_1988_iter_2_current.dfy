predicate ValidInput(s: string)
{
    |s| >= 2 &&
    (s[|s|-1] == '\n' || (|s| >= 2 && s[|s|-2..] == "\n")) &&
    exists lines :: lines == split_lines(s) && |lines| >= 1 &&
    exists lines, t :: lines == split_lines(s) && t == parse_int(lines[0]) && t >= 1 &&
    (forall lines, t :: 
        (lines == split_lines(s) && t == parse_int(lines[0])) ==> 
        |lines| >= 1 + 2*t) &&
    (forall lines, t, i :: 
        (lines == split_lines(s) && t == parse_int(lines[0]) && 0 <= i < t) ==> 
        (exists n :: n == parse_int(lines[1 + 2*i]) && n >= 1 && n <= 5000 && 
         |lines[1 + 2*i + 1]| == n)) &&
    (forall lines, t, i :: 
        (lines == split_lines(s) && t == parse_int(lines[0]) && 0 <= i < t) ==> 
        (forall j :: 0 <= j < |lines[1 + 2*i + 1]| ==> 
         lines[1 + 2*i + 1][j] in "abcdefghijklmnopqrstuvwxyz"))
}

predicate ValidOutput(result: string)
{
    |result| >= 0 &&
    (result == "" || result[|result|-1] == '\n')
}

function transform_string(input_str: string, n: int, k: int): string
  requires 1 <= k <= n
  requires |input_str| == n
{
    var i := k - 1;
    if (n - i) % 2 == 0 then
        input_str[i..] + input_str[..i]
    else
        input_str[i..] + reverse_string(input_str[..i])
}

predicate is_lexicographically_optimal(result_str: string, input_str: string, n: int, k: int)
  requires |input_str| == n
{
    1 <= k <= n &&
    (exists transformation :: 
      transformation == transform_string(input_str, n, k) && result_str == transformation &&
      forall other_k :: 1 <= other_k <= n ==> 
        result_str <= transform_string(input_str, n, other_k))
}

// <vc-helpers>
function split_lines(s: string): seq<string>
{
  split_lines_helper(s, 0, 0, [])
}

function split_lines_helper(s: string, start: nat, i: nat, acc: seq<string>): seq<string>
  requires start <= i <= |s|
  decreases |s| - i
{
  if i == |s| then
    if start < i then acc + [s[start..i]] else acc
  else if s[i] == '\n' then
    split_lines_helper(s, i+1, i+1, acc + [s[start..i]])
  else
    split_lines_helper(s, start, i+1, acc)
}

function parse_int(s: string): int
{
  if |s| == 0 then 0
  else parse_int_helper(s, 0, 0)
}

function parse_int_helper(s: string, i: nat, acc: int): int
  requires i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else if '0' <= s[i] <= '9' then
    parse_int_helper(s, i+1, acc * 10 + (s[i] as int - '0' as int))
  else acc
}

function reverse_string(s: string): string
{
  if |s| == 0 then ""
  else reverse_string_helper(s, |s| - 1, "")
}

function reverse_string_helper(s: string, i: int, acc: string): string
  requires -1 <= i < |s|
  decreases i + 1
{
  if i < 0 then acc
  else reverse_string_helper(s, i - 1, acc + [s[i]])
}

function int_to_string(n: int): string
  requires n >= 0
{
  if n == 0 then "0"
  else int_to_string_helper(n, "")
}

function int_to_string_helper(n: int, acc: string): string
  requires n >= 0
  decreases n
{
  if n == 0 then 
    if |acc| == 0 then "0" else acc
  else 
    var digit := (n % 10 + '0' as int) as char;
    int_to_string_helper(n / 10, [digit] + acc)
}

function find_optimal_k(input_str: string, n: int): int
  requires |input_str| == n
  requires n >= 1
  ensures 1 <= find_optimal_k(input_str, n) <= n
{
  find_optimal_k_helper(input_str, n, 1, 1, transform_string(input_str, n, 1))
}

function find_optimal_k_helper(input_str: string, n: int, current_k: int, best_k: int, best_result: string): int
  requires |input_str| == n
  requires n >= 1
  requires 1 <= current_k <= n + 1
  requires 1 <= best_k <= n
  decreases n + 1 - current_k
  ensures 1 <= find_optimal_k_helper(input_str, n, current_k, best_k, best_result) <= n
{
  if current_k > n then best_k
  else
    var current_result := transform_string(input_str, n, current_k);
    if current_result < best_result then
      find_optimal_k_helper(input_str, n, current_k + 1, current_k, current_result)
    else
      find_optimal_k_helper(input_str, n, current_k + 1, best_k, best_result)
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
  requires ValidInput(s)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var lines := split_lines(s);
  var t := parse_int(lines[0]);
  var result_str := "";
  
  var case_idx := 0;
  while case_idx < t
    invariant 0 <= case_idx <= t
    invariant |lines| >= 1 + 2*t
    invariant case_idx == 0 ==> result_str == ""
    invariant case_idx > 0 ==> |result_str| > 0 && result_str[|result_str|-1] == '\n'
  {
    var n := parse_int(lines[1 + 2*case_idx]);
    var input_str := lines[1 + 2*case_idx + 1];
    
    var optimal_k := find_optimal_k(input_str, n);
    var optimal_result := transform_string(input_str, n, optimal_k);
    
    result_str := result_str + int_to_string(optimal_k) + " " + optimal_result + "\n";
    
    case_idx := case_idx + 1;
  }
  
  return result_str;
}
// </vc-code>

