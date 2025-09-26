// <vc-preamble>
predicate ValidInput(input: string)
{
  |input| > 0 && has_two_lines(input) && 
  var lines := [get_first_line(input), get_second_line(input)];
  |lines| >= 2 &&
  var n := parse_int(lines[0]);
  var pts := lines[1];
  n >= 3 && |pts| == n && is_valid_digit_string(pts)
}

predicate CanMakeAllZero(n: int, pts: string)
  requires n > 0 && |pts| == n && is_valid_digit_string(pts)
{
  all_dft_tests_pass(n, pts)
}

predicate dft_test_passes(n: int, pts: string, j: int)
  requires n > 0 && |pts| == n && is_valid_digit_string(pts) && j > 0
{
  gcd(n, j) != 1 || 
  (var pi := 3.14159265359;
   var x_terms := seq(n, i requires 0 <= i < n => 
     (char_to_digit(pts[i]) as real) * cos_approx(2.0 * pi * (i as real) * (j as real) / (n as real)));
   var y_terms := seq(n, i requires 0 <= i < n => 
     (char_to_digit(pts[i]) as real) * sin_approx(2.0 * pi * (i as real) * (j as real) / (n as real)));
   var sum_x := sum_real_sequence(x_terms);
   var sum_y := sum_real_sequence(y_terms);
   abs_real(sum_x) < 0.000001 && abs_real(sum_y) < 0.000001)
}

predicate all_dft_tests_pass(n: int, pts: string)
  requires n > 0 && |pts| == n && is_valid_digit_string(pts)
{
  var primes := [7,11,13,17,19,23,29,31,37,1193,1663,2711,4007,65537];
  forall i :: 0 <= i < |primes| ==> dft_test_passes(n, pts, primes[i])
}
// </vc-preamble>

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  requires a > 0 || b > 0
{
  if a == 0 then b
  else if b == 0 then a  
  else if a >= b then gcd(a - b, b)
  else gcd(a, b - a)
}

function abs_real(x: real): real
{
  if x >= 0.0 then x else -x
}

function cos_approx(x: real): real
{
  var x2 := x * x;
  var x4 := x2 * x2;
  var x6 := x4 * x2;
  1.0 - x2/2.0 + x4/24.0 - x6/720.0
}

function sin_approx(x: real): real  
{
  var x2 := x * x;
  var x3 := x * x2;
  var x5 := x3 * x2;
  var x7 := x5 * x2;
  x - x3/6.0 + x5/120.0 - x7/5040.0
}

function char_to_digit(c: char): int
{
  if '0' <= c <= '9' then (c as int) - ('0' as int) else 0
}

function parse_int(s: string): int
{
  if |s| == 0 then 0
  else if |s| == 1 then char_to_digit(s[0])
  else parse_int(s[..|s|-1]) * 10 + char_to_digit(s[|s|-1])
}

predicate is_valid_digit_char(c: char)
{
  '0' <= c <= '9'
}

predicate is_valid_digit_string(s: string)
{
  forall i :: 0 <= i < |s| ==> is_valid_digit_char(s[i])
}

function find_newline(input: string, start: int): int
  requires 0 <= start <= |input|
  ensures start <= find_newline(input, start) <= |input|
  decreases |input| - start
{
  if start >= |input| then |input|
  else if input[start] == '\n' then start
  else find_newline(input, start + 1)
}

function get_first_line(input: string): string
{
  var newline_pos := find_newline(input, 0);
  input[0..newline_pos]
}

function get_second_line(input: string): string
{
  var first_newline := find_newline(input, 0);
  if first_newline >= |input| then ""
  else 
    var start := first_newline + 1;
    if start > |input| then ""
    else
      var second_newline := find_newline(input, start);
      input[start..second_newline]
}

predicate has_two_lines(input: string)
{
  var first_newline := find_newline(input, 0);
  first_newline < |input| && first_newline + 1 <= |input|
}

function sum_real_sequence(s: seq<real>): real
{
  if |s| == 0 then 0.0 else s[0] + sum_real_sequence(s[1..])
}

method split_lines(input: string) returns (lines: seq<string>)
  ensures |lines| >= 0
{
  lines := [];
  var start := 0;
  var i := 0;

  while i <= |input|
    invariant 0 <= start <= i <= |input| + 1
    invariant |lines| >= 0
  {
    if i == |input| || input[i] == '\n' {
      if start < i {
        lines := lines + [input[start..i]];
      }
      start := i + 1;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires |input| > 0
  ensures result == "YES" || result == "NO"
// </vc-spec>
// <vc-code>
{
  var lines := split_lines(input);
  if |lines| < 2 {
    return "NO";
  }

  var n := parse_int(lines[0]);
  var pts := lines[1];

  if n < 3 || |pts| != n {
    return "NO";  
  }

  if !is_valid_digit_string(pts) {
    return "NO";
  }

  var primes := [7,11,13,17,19,23,29,31,37,1193,1663,2711,4007,65537];
  var pi := 3.14159265359;

  var i := 0;
  while i < |primes|
    invariant 0 <= i <= |primes|
  {
    var j := primes[i];
    if gcd(n, j) == 1 {
      var x: real := 0.0;
      var y: real := 0.0;

      var point_idx := 0;
      while point_idx < n
        invariant 0 <= point_idx <= n
      {
        var k := char_to_digit(pts[point_idx]);
        var angle := 2.0 * pi * (point_idx as real) * (j as real) / (n as real);
        var tmpCall1 := cos_approx(angle);
        x := x + (k as real) * tmpCall1;
        var tmpCall2 := sin_approx(angle);
        y := y + (k as real) * tmpCall2;
        point_idx := point_idx + 1;
      }

      if !(abs_real(x) < 0.000001 && abs_real(y) < 0.000001) {
        return "NO";
      }
    }
    i := i + 1;
  }

  return "YES";
}
// </vc-code>
