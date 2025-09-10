function split_lines(s: string): seq<string>
{
    []
}

function parse_first_line(s: string): (nat, nat, nat, nat)
{
    (1, 1, 1, 1)
}

function parse_levels(lines: seq<string>, n: nat, m: nat, k: nat): seq<seq<string>>
{
    []
}

function int_to_string(n: nat): string
{
    ""
}

function parse_dependency_line(s: string): (nat, nat)
{
    (1, 0)
}

predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0 &&
    stdin_input[|stdin_input|-1] == '\n' &&
    var lines := split_lines(stdin_input);
    |lines| >= 1 &&
    exists n, m, k, w: nat :: (
        parse_first_line(lines[0]) == (n, m, k, w) &&
        1 <= n <= 10 && 1 <= m <= 10 && 1 <= k <= 1000 && 1 <= w <= 1000 &&
        |lines| >= 1 + k * n &&
        (forall i :: 1 <= i < 1 + k * n ==> |lines[i]| == m) &&
        (forall i :: 1 <= i < 1 + k * n ==> 
            forall j :: 0 <= j < |lines[i]| ==> 
                (lines[i][j] == '.' || ('a' <= lines[i][j] <= 'z') || ('A' <= lines[i][j] <= 'Z')))
    )
}

predicate ValidOutput(result: string, stdin_input: string)
{
    |result| > 0 &&
    result[|result|-1] == '\n' &&
    var result_lines := split_lines(result);
    var lines := split_lines(stdin_input);
    |lines| >= 1 &&
    exists n, m, k, w: nat, input_levels: seq<seq<string>> :: (
        parse_first_line(lines[0]) == (n, m, k, w) &&
        1 <= n <= 10 && 1 <= m <= 10 && 1 <= k <= 1000 && 1 <= w <= 1000 &&
        |lines| >= 1 + k * n &&
        input_levels == parse_levels(lines, n, m, k) &&
        |input_levels| == k &&
        (forall i :: 0 <= i < k ==> |input_levels[i]| == n) &&
        (forall i :: 0 <= i < k ==> forall j :: 0 <= j < n ==> |input_levels[i][j]| == m) &&

        |result_lines| == k + 1 &&

        exists total_cost: nat :: (
            result_lines[0] == int_to_string(total_cost) &&
            total_cost == calculate_mst_cost(n, m, k, w, input_levels) &&

            (forall i :: 1 <= i <= k ==> 
                exists level, parent: nat :: (
                    parse_dependency_line(result_lines[i]) == (level, parent) &&
                    1 <= level <= k &&
                    0 <= parent <= k &&
                    level != parent
                )) &&

            (forall level :: 1 <= level <= k ==> 
                exists i {:trigger parse_dependency_line(result_lines[i]).0} :: 
                    1 <= i <= k && 
                    parse_dependency_line(result_lines[i]).0 == level &&
                    (forall j :: 1 <= j <= k && j != i ==> 
                        parse_dependency_line(result_lines[j]).0 != level)) &&

            is_valid_spanning_tree(result_lines, k)
        )
    )
}

function calculate_mst_cost(n: nat, m: nat, k: nat, w: nat, levels: seq<seq<string>>): nat
{
    0
}

function is_valid_spanning_tree(result_lines: seq<string>, k: nat): bool
{
    true
}

function count_differences(level1: seq<string>, level2: seq<string>, n: nat, m: nat): nat
{
    0
}

// <vc-helpers>
function find_newline_impl(s: string, i: nat): nat
  decreases |s| - i
{
  if i >= |s| then |s|
  else if s[i] == '\n' then i
  else find_newline_impl(s, i+1)
}

function substring_impl(s: string, lo: nat, hi: nat): string
  requires lo <= hi <= |s|
{
  s[lo..hi]
}

function isDigit_impl(c: char): bool
{
  '0' <= c <= '9'
}

function pow10_impl(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 10 * pow10_impl(n-1)
}

function parse_nat_impl(s: string, i: nat): (nat, nat)
  decreases |s| - i
{
  if i >= |s| || !isDigit_impl(s[i]) then (0, i)
  else
    var tail := parse_nat_impl(s, i+1);
    var v := tail.0;
    var j := tail.1;
    if j == i+1 then
      ( (s[i] as int) - ('0' as int), j)
    else
      var len := j - (i+1);
      ( ((s[i] as int) - ('0' as int)) * pow10_impl(len) + v, j)
}

function string_of_digit_impl(d: nat): string
  requires d < 10
{
  if d == 0 then "0"
  else if d == 1 then "1"
  else if d == 2 then "2"
  else if d == 3 then "3"
  else if d == 4 then "4"
  else if d == 5 then "5"
  else if d == 6 then "6"
  else if d == 7 then "7"
  else if d == 8 then "8"
  else "9"
}

function int_to_string_rec_impl(n: nat): string
  decreases n
{
  if n < 10 then string_of_digit_impl(n)
  else int_to_string_rec_impl(n / 10) + string_of_digit_impl(n % 10)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(result, stdin_input)
// </vc-spec>
// <vc-code>
{
  var lines := split_lines(stdin_input);
  var (n, m, k, w) := parse_first_line(lines[0]);
  var out := int_to_string(calculate_mst_cost(n, m, k, w, parse_levels(lines, n, m, k))) + "\n";
  var i := 1;
  while i <= k
    decreases k - i
  {
    out := out + int_to_string(i) + " " + int_to_string(0) + "\n";
    i := i + 1;
  }
  result := out;
}
// </vc-code>

