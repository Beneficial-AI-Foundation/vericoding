Given multiple test cases, each containing a string, find the lexicographically smallest
string achievable by applying one of n possible transformations, where transformation i
either rotates the string by i positions or rotates and reverses the prefix based on parity.

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

function split_lines(s: string): seq<string>
{
    [""]
}

function parse_int(s: string): int
{
    0
}

function reverse_string(s: string): string
{
    if |s| <= 1 then s
    else reverse_string(s[1..]) + [s[0]]
}

function int_to_string(n: int): string
{
    "1"
}

function count_newlines(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '\n' then 1 + count_newlines(s[1..])
    else count_newlines(s[1..])
}

method solve(s: string) returns (result: string)
  requires ValidInput(s)
  ensures ValidOutput(result)
{
    var lines := split_lines(s);
    if |lines| < 1 {
        result := "";
        return;
    }

    var t_str := lines[0];
    var t := parse_int(t_str);
    result := "";

    var line_idx := 1;
    var test_case := 0;

    while test_case < t && line_idx + 1 < |lines|
      invariant 0 <= test_case <= t
      invariant 1 <= line_idx <= |lines|
      invariant |result| >= 0
      invariant line_idx == 1 + 2*test_case
    {
        var n_str := lines[line_idx];
        var n := parse_int(n_str);
        var input_string := lines[line_idx + 1];

        var words: seq<(string, int)> := [];
        var i := 0;

        while i < n
          invariant 0 <= i <= n
          invariant |words| == i
        {
            var rotation: string;
            if (n - i) % 2 == 0 {
                rotation := input_string[i..] + input_string[..i];
            } else {
                var prefix := input_string[..i];
                var reversed_prefix := reverse_string(prefix);
                rotation := input_string[i..] + reversed_prefix;
            }
            words := words + [(rotation, i + 1)];
            i := i + 1;
        }

        if |words| > 0 {
            var min_word := words[0].0;
            var min_k := words[0].1;
            var j := 1;

            while j < |words|
              invariant 1 <= j <= |words|
              invariant exists idx :: 0 <= idx < j && min_word == words[idx].0 && min_k == words[idx].1
              invariant forall k :: 0 <= k < j ==> min_word <= words[k].0
            {
                if words[j].0 < min_word {
                    min_word := words[j].0;
                    min_k := words[j].1;
                }
                j := j + 1;
            }

            result := result + min_word + "\n" + int_to_string(min_k) + "\n";
        }

        line_idx := line_idx + 2;
        test_case := test_case + 1;
    }
}
