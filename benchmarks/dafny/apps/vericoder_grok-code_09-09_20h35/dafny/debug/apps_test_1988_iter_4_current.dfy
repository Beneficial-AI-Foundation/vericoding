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
function reverse_string(s: string): string
{
    if |s| == 0 then ""
    else reverse_string(s[1..]) + [s[0]]
}

function find_newline(s: string, start: nat): nat
{
    if start >= |s| then |s|
    else if s[start] == '\n' then start
    else find_newline(s, start + 1)
}

function split_lines(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var p := find_newline(s, 0);
        if p == |s| then [s]
        else [s[..p]] + split_lines(s[p+1..])
}

function parse_int(s: string): int
{
    if |s| == 0 then 0
    else (parse_int(s[..|s|-1]) * 10) + ((s[|s|-1] as int) - ('0' as int))
}

method find_optimal_k(input_str: string, n: int) returns (best_k: int)
  requires 1 <= n <= 5000 && |input_str| == n
  ensures 1 <= best_k <= n
  ensures forall kk :: 1 <= kk <= n ==> transform_string(input_str, n, best_k) <= transform_string(input_str, n, kk)
{
    var min_str := transform_string(input_str, n, 1);
    best_k := 1;
    var k := 2;
    while k <= n
        invariant 2 <= k <= n+1
        invariant min_str == transform_string(input_str, n, best_k)
        invariant forall kk :: 1 <= kk < k ==> transform_string(input_str, n, kk) >= min_str
    {
        var current := transform_string(input_str, n, k);
        if current < min_str
        {
            min_str := current;
            best_k := k;
        }
        k := k + 1;
    }
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
    var result := "";
    var i := 0;
    while i < t
    {
        var n := parse_int(lines[1 + 2*i]);
        var input_str := lines[1 + 2*i + 1];
        var best_k := find_optimal_k(input_str, n);
        var transformed := transform_string(input_str, n, best_k);
        result := result + transformed + "\n";
        i := i + 1;
    }
}
// </vc-code>

