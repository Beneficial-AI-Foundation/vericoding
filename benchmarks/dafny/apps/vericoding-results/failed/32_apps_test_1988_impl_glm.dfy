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
function split_lines(s: string): seq<string> {
  if s == "" then []
  else
    var i := 0;
    var lines := [];
    while i < |s|
      invariant 0 <= i <= |s|
    {
      var j := i;
      while j < |s| && s[j] != '\n'
        invariant i <= j <= |s|
      {
        j := j + 1;
      }
      lines := lines + [s[i..j]];
      i := j + 1;
    }
    // Remove trailing empty string if last character is newline
    if |lines| > 0 && lines[|lines|-1] == "" then
      lines[..|lines|-1]
    else
      lines
}

function parse_int(s: string): int {
  if s == "" then 0
  else
    var i := 0;
    var n := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant n >= 0
    {
      var digit := s[i] - '0';
      n := n * 10 + digit;
      i := i + 1;
    }
    n
}

function reverse_string(s: string): string {
  var i := |s| - 1;
  var result := "";
  while i >= 0
    invariant -1 <= i < |s|
    invariant |result| == |s| - 1 - i
  {
    result := result + s[i];
    i := i - 1;
  }
  result
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
  var i := 0;

  while i < t
    invariant 0 <= i <= t
    invariant result_str == "" ==> i == 0
    invariant result_str != "" ==> result_str[|result_str|-1] == '\n'
  {
    var n := parse_int(lines[1 + 2*i]);
    var str := lines[1 + 2*i + 1];
    var min_str := str;
    var k := 1;
    while k <= n
      invariant 1 <= k <= n+1
      invariant k == 1 || (forall j :: 1 <= j < k ==> min_str <= transform_string(str, n, j))
      invariant k == 1 || (exists j :: 1 <= j < k && min_str == transform_string(str, n, j))
    {
      var candidate := transform_string(str, n, k);
      if candidate < min_str then
        min_str := candidate;
      k := k + 1;
    }
    result_str := result_str + min_str + "\n";
    i := i + 1;
  }
  return result_str;
}
// </vc-code>

