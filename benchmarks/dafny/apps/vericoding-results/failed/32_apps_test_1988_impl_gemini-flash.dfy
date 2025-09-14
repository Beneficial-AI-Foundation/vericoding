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
function parse_int(s: string) : int
  reads s
  // Requires s to contain only digits. This simplifies reasoning about the helper and avoids
  // needing error handling for non-digit characters.
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
{
  if s == "" then 0 else (
    var x := 0; 
    var i := 0; 
    while i < |s| 
      invariant 0 <= i <= |s| 
      invariant x == parse_int_helper(s[..i])
      invariant forall k :: 0 <= k < i ==> '0' <= s[k] <= '9'
    { 
      x := x * 10 + (s[i] as int - '0' as int); 
      i := i + 1; 
    } 
    return x;
  )
}

function parse_int_helper(s: string) : int
  reads s
  // A helper function to compute the integer value of a string, used in invariants
  // This helps break the circular dependency between parse_int's body and its invariant relation.
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
{
  if s == "" then 0
  else parse_int_helper(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function split_lines(s: string) : seq<string>
  reads s
{
  if s == "" then []
  else if s[0] == '\n' then [""] + split_lines(s[1..])
  else
    var i := 0;
    while i < |s| && s[i] != '\n'
    invariant 0 <= i <= |s|
    {
      i := i + 1;
    }
    if i == |s| then [s]
    else [s[..i]] + split_lines(s[i+1..])
}

function reverse_string(s: string): string
  reads s
  ensures |reverse_string(s)| == |s|
{
  if |s| == 0 then ""
  else reverse_string(s[1..]) + s[0..1]
}

lemma lemma_string_length_concat(s1: string, s2: string)
  ensures |s1 + s2| == |s1| + |s2|
{}

lemma lemma_string_slice_concat(s: string, i: int)
  requires 0 <= i <= |s|
  ensures s[..i] + s[i..] == s
{}

lemma lemma_string_slice_length(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
  ensures |s[i..j]| == j - i
{}

lemma lemma_string_slice_length_full(s: string, i: int)
  requires 0 <= i <= |s|
  ensures |s[i..]| == |s| - i
{}

lemma lemma_string_slice_length_prefix(s: string, i: int)
  requires 0 <= i <= |s|
  ensures |s[..i]| == i
{}

lemma lemma_string_lexicographical_comparison(s1: string, s2: string, s3: string)
  ensures (s1 <= s2 && s2 <= s3) ==> s1 <= s3
{}
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
    var result_lines: seq<string> := [];

    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant |result_lines| == i
        invariant forall k :: 0 <= k < i ==> is_lexicographically_optimal(result_lines[k], lines[1 + 2*k + 1], parse_int(lines[1 + 2*k]), 1)
    {
        var n_str := lines[1 + 2*i];
        assert forall kk :: 0 <= kk < |n_str| ==> '0' <= n_str[kk] <= '9'; // From ValidInput
        var n := parse_int(n_str);
        var input_str := lines[1 + 2*i + 1];
        
        var best_str := transform_string(input_str, n, 1);
        var k_prime := 2;
        while k_prime <= n
            invariant 1 <= k_prime <= n + 1
            invariant forall kk :: 1 <= kk < k_prime ==> best_str <= transform_string(input_str, n, kk)
            invariant 1 <= n // because it's extracted from ValidInput
            invariant |input_str| == n // from ValidInput
        {
            var current_str := transform_string(input_str, n, k_prime);
            if current_str < best_str {
                best_str := current_str;
            }
            k_prime := k_prime + 1;
        }
        result_lines := result_lines + [best_str];
        i := i + 1;
    }
    
    result := "";
    i := 0;
    while i < |result_lines|
        invariant 0 <= i <= |result_lines|
        invariant (i == 0 && result == "") || (i > 0 && result[|result|-1] == '\n')
        invariant result == (if i == 0 then "" else (var temp_res := ""; forall k :: 0 <= k < i ==> temp_res := temp_res + result_lines[k] + "\n"; temp_res))
    {
        result := result + result_lines[i] + "\n";
        i := i + 1;
    }
    return result;
}
// </vc-code>

