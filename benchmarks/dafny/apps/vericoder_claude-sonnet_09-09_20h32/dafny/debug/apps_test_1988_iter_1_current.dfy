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
function method reverse_string(s: string): string
{
    if |s| == 0 then ""
    else reverse_string(s[1..]) + [s[0]]
}

function method split_lines(s: string): seq<string>
{
    if |s| == 0 then []
    else if |s| == 1 then 
        if s[0] == '\n' then [""] else [s]
    else
        var first_newline := find_first_newline(s, 0);
        if first_newline == -1 then [s]
        else [s[..first_newline]] + split_lines(s[first_newline+1..])
}

function method find_first_newline(s: string, start: int): int
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else find_first_newline(s, start + 1)
}

function method parse_int(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then 
        if '0' <= s[0] <= '9' then (s[0] as int) - ('0' as int) else 0
    else
        var first_digit := if '0' <= s[0] <= '9' then (s[0] as int) - ('0' as int) else 0;
        first_digit * power_of_10(|s| - 1) + parse_int(s[1..])
}

function method power_of_10(n: int): int
{
    if n <= 0 then 1
    else 10 * power_of_10(n - 1)
}

function method find_optimal_k(input_str: string, n: int): int
  requires |input_str| == n && n >= 1
  ensures 1 <= find_optimal_k(input_str, n) <= n
{
    find_optimal_k_helper(input_str, n, 1, 1)
}

function method find_optimal_k_helper(input_str: string, n: int, current_k: int, best_k: int): int
  requires |input_str| == n && n >= 1
  requires 1 <= current_k <= n + 1
  requires 1 <= best_k <= n
  ensures 1 <= find_optimal_k_helper(input_str, n, current_k, best_k) <= n
{
    if current_k > n then best_k
    else
        var current_transform := transform_string(input_str, n, current_k);
        var best_transform := transform_string(input_str, n, best_k);
        var new_best := if current_transform < best_transform then current_k else best_k;
        find_optimal_k_helper(input_str, n, current_k + 1, new_best)
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
    var result_parts: seq<string> := [];
    
    var i := 0;
    while i < t
    {
        var n := parse_int(lines[1 + 2*i]);
        var input_str := lines[1 + 2*i + 1];
        var optimal_k := find_optimal_k(input_str, n);
        var transformed := transform_string(input_str, n, optimal_k);
        result_parts := result_parts + [transformed];
        i := i + 1;
    }
    
    result := "";
    var j := 0;
    while j < |result_parts|
    {
        result := result + result_parts[j] + "\n";
        j := j + 1;
    }
}
// </vc-code>

