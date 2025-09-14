predicate is_valid_input(input: string)
    requires |input| > 0
{
    var lines := parse_lines(input);
    |lines| >= 2 && |lines[0]| == 3 && |lines[1]| == 3
}

function count_matches_from_input(input: string): int
    requires |input| > 0
    requires is_valid_input(input)
    ensures 0 <= count_matches_from_input(input) <= 3
{
    var lines := parse_lines(input);
    count_matches(lines[0], lines[1])
}

function count_matches(s: string, t: string): int
    requires |s| == |t| == 3
    ensures 0 <= count_matches(s, t) <= 3
    ensures count_matches(s, t) == 
        (if s[0] == t[0] then 1 else 0) +
        (if s[1] == t[1] then 1 else 0) +
        (if s[2] == t[2] then 1 else 0)
{
    (if s[0] == t[0] then 1 else 0) +
    (if s[1] == t[1] then 1 else 0) +
    (if s[2] == t[2] then 1 else 0)
}

function compute_result(input: string): string
    requires |input| > 0
    ensures |compute_result(input)| >= 2
    ensures compute_result(input)[|compute_result(input)|-1] == '\n'
    ensures compute_result(input)[0] in {'0', '1', '2', '3'}
    ensures is_valid_input(input) ==> 
        compute_result(input) == int_to_string(count_matches_from_input(input)) + "\n"
    ensures !is_valid_input(input) ==> compute_result(input) == "0\n"
{
    var lines := parse_lines(input);
    if |lines| < 2 then "0\n"
    else if |lines[0]| != 3 || |lines[1]| != 3 then "0\n"
    else int_to_string(count_matches(lines[0], lines[1])) + "\n"
}

// <vc-helpers>
function index_of(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == c then 0 else 1 + index_of(s[1..], c)
}

function parse_lines(input: string): seq<string>
  decreases |input|
{
  if |input| == 0 then []
  else
    var i := index_of(input, '\n');
    if i == |input| then [input]
    else [ input[..i] ] + parse_lines(input[i+1..])
}

function int_to_string(n: int): string
  requires n >= 0
  decreases n
{
  if n < 10 then
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else "9"
  else
    int_to_string(n / 10) + (
      if n % 10 == 0 then "0"
      else if n % 10 == 1 then "1"
      else if n % 10 == 2 then "2"
      else if n % 10 == 3 then "3"
      else if n % 10 == 4 then "4"
      else if n % 10 == 5 then "5"
      else if n % 10 == 6 then "6"
      else if n % 10 == 7 then "7"
      else if n % 10 == 8 then "8"
      else "9")
}

lemma compute_result_props(input: string)
  requires |input| > 0
  ensures |compute_result(input)| >= 2
  ensures compute_result(input)[|compute_result(input)|-1] == '\n'
  ensures compute_result(input)[0] in {'0','1','2','3'}
{
  var lines := parse_lines(input);
  if |lines| < 2 {
    assert compute_result(input) == "0\n";
    assert |compute_result(input)| == 2;
    assert compute_result(input)[|compute_result(input)|-1] == '\n';
    assert compute_result(input)[0] in {'0','1','2','3'};
  } else if |lines[0]| != 3 || |lines[1]| != 3 {
    assert compute_result(input) == "0\n";
    assert |compute_result(input)| == 2;
    assert compute_result(input)[|compute_result(input)|-1] == '\n';
    assert compute_result(input)[0] in {'0','1','2','3'};
  } else {
    var n := count_matches(lines[0], lines[1]);
    assert 0 <= n <= 3;
    assert compute_result(input) == int_to_string(n) + "\n";
    if n == 0 {
      assert int_to_string(n) == "0";
      assert int_to_string(n)[0] == '0';
    } else if n == 1 {
      assert int_to_string(n) == "1";
      assert int_to_string(n)[0] == '1';
    } else if n == 2 {
      assert int_to_string(n) == "2";
      assert int_to_string(n)[0] == '2';
    } else {
      assert int_to_string(n) == "3";
      assert int_to_string(n)[0] == '3';
    }
    assert |int_to_string(n)| >= 1;
    assert |compute_result(input)| >= 2;
    assert compute_result(input)[|compute_result(input)|-1] == '\n';
    assert compute_result(input)[0] in {'0','1','2','3'};
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == compute_result(input)
    ensures |result| >= 2 && result[|result|-1] == '\n'
    ensures result[0] in
// </vc-spec>
// <vc-code>
{
  result := compute_result(input);
  compute_result_props(input);
}
// </vc-code>

