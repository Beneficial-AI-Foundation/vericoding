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
  ensures |split_lines(s)| >= 1
  ensures s == "" ==> |split_lines(s)| == 1 && split_lines(s)[0] == ""
  ensures s != "" ==> split_lines(s)[|split_lines(s)|-1] == "" || s[|s|-1] == '\n'

function parse_int(s: string): int
  ensures parse_int("0") == 0
  ensures forall n: nat :: parse_int(int_to_string(n)) == n

function reverse_string(s: string): string
  ensures |reverse_string(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> reverse_string(s)[i] == s[|s| - 1 - i]

lemma reverse_string_lemma(s: string)
  ensures reverse_string(reverse_string(s)) == s

lemma transform_string_symmetry(input_str: string, n: int, k: int)
  requires |input_str| == n
  requires 1 <= k <= n
  ensures transform_string(reverse_string(input_str), n, n - k + 1) == reverse_string(transform_string(input_str, n, k))

function compare_strings(a: string, b: string): int
  ensures compare_strings(a, b) == -compare_strings(b, a)
  ensures a <= b <==> compare_strings(a, b) <= 0

lemma transform_string_same_length(input_str: string, n: int, k: int)
  requires |input_str| == n
  requires 1 <= k <= n
  ensures |transform_string(input_str, n, k)| == n

function int_to_string(n: nat): string
  ensures |int_to_string(n)| >= 1

lemma int_to_string_inverse(n: nat)
  ensures parse_int(int_to_string(n)) == n

lemma compare_transform_strings(input_str: string, n: int, k1: int, k2: int)
  requires |input_str| == n
  requires 1 <= k1 <= n && 1 <= k2 <= n
  ensures transform_string(input_str, n, k1) == transform_string(input_str, n, k2) ==> k1 == k2
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
  result := "";
  
  var i := 0;
  while i < t
    invariant 0 <= i <= t
    invariant ValidOutput(result)
  {
    var n := parse_int(lines[1 + 2*i]);
    var input_str := lines[1 + 2*i + 1];
    
    var best_k := 1;
    var best_str := transform_string(input_str, n, 1);
    
    var k := 2;
    while k <= n
      invariant 1 <= k <= n + 1
      invariant best_k >= 1 && best_k < k
      invariant |best_str| == n
      invariant is_lexicographically_optimal(best_str, input_str, n, best_k)
    {
      var current_str := transform_string(input_str, n, k);
      if current_str < best_str {
        best_str := current_str;
        best_k := k;
      }
      k := k + 1;
    }
    
    result := result + int_to_string(best_k) + "\n";
    i := i + 1;
  }
}
// </vc-code>

