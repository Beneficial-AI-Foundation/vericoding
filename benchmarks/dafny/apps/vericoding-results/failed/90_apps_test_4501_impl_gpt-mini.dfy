predicate valid_input_format(stdin_input: string)
{
    var lines := split_lines_func(stdin_input);
    |lines| >= 2 &&
    var first_line := split_spaces_func(lines[0]);
    var second_line := split_spaces_func(lines[1]);
    |first_line| == 2 &&
    is_valid_integer(first_line[0]) &&
    is_valid_integer(first_line[1]) &&
    var N := string_to_int_func(first_line[0]);
    var A := string_to_int_func(first_line[1]);
    1 <= N <= 50 &&
    1 <= A <= 50 &&
    |second_line| == N &&
    (forall j | 0 <= j < |second_line| :: 
        is_valid_integer(second_line[j]) &&
        1 <= string_to_int_func(second_line[j]) <= 50)
}

predicate is_valid_output(output: string)
{
    |output| > 1 && 
    output[|output|-1] == '\n' &&
    var result_str := output[..|output|-1];
    is_valid_integer(result_str) &&
    string_to_int_func(result_str) >= 0
}

predicate output_represents_correct_count(stdin_input: string, output: string)
    requires valid_input_format(stdin_input)
    requires is_valid_output(output)
{
    var lines := split_lines_func(stdin_input);
    var first_line := split_spaces_func(lines[0]);
    var second_line := split_spaces_func(lines[1]);
    var N := string_to_int_func(first_line[0]);
    var A := string_to_int_func(first_line[1]);
    var cards := seq(N, i requires 0 <= i < N => string_to_int_func(second_line[i]));
    var result := string_to_int_func(output[..|output|-1]);
    result == count_valid_selections(cards, A)
}

function count_valid_selections(cards: seq<int>, A: int): int
{
    var differences := seq(|cards|, i requires 0 <= i < |cards| => cards[i] - A);
    var total := count_zero_sum_subsets(differences);
    if total > 0 then total - 1 else 0
}

function count_zero_sum_subsets(differences: seq<int>): nat
{
    if |differences| == 0 then 1
    else
        var rest_count := count_zero_sum_subsets(differences[1..]);
        rest_count + count_subsets_with_sum(differences[1..], -differences[0])
}

function count_subsets_with_sum(differences: seq<int>, target: int): nat
{
    if |differences| == 0 then if target == 0 then 1 else 0
    else
        count_subsets_with_sum(differences[1..], target) +
        count_subsets_with_sum(differences[1..], target - differences[0])
}

// <vc-helpers>
const DIGITS: string := "0123456789"

function index_of_newline(s: string, i: nat): nat
  decreases |s| - i
{
  if i >= |s| then |s|
  else if s[i] == '\n' then i
  else index_of_newline(s, i + 1)
}

function split_lines_func(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else
    var i := index_of_newline(s, 0);
    if i >= |s| then [s]
    else [s[..i]] + split_lines_func(s[i+1..])
}

function index_of_space(s: string, i: nat): nat
  decreases |s| - i
{
  if i >= |s| then |s|
  else if s[i] == ' ' then i
  else index_of_space(s, i + 1)
}

function split_spaces_func(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else
    var i := index_of_space(s, 0);
    if i >= |s| then [s]
    else [s[..i]] + split_spaces_func(s[i+1..])
}

function index_of_digit(c: char, i: nat): nat
  decreases 10 - i
{
  if i >= 10 then 0
  else if DIGITS[i..i+1][0] == c then i
  else index_of_digit(c, i + 1)
}

predicate is_valid_integer(s: string)
{
  |s| > 0 &&
  (forall k :: 0 <= k < |s| ==>
      exists d :: {:trigger (DIGITS[d..d+1][0] == s[k])} 0 <= d < 10 && DIGITS[d..d+1][0] == s[k])
}

function string_to_int_func(s: string): int
  requires is_valid_integer(s)
  decreases |s|
{
  if |s| == 1 then index_of_digit(s[0], 0)
  else string_to_int_func(s[..|s|-1]) * 10 + index_of_digit(s[|s|-1], 0)
}

function int_to_string_rec(n: nat): string
  decreases n
{
  if n == 0 then ""
  else
    var q := n / 10;
    var r := n % 10;
    int_to_string_rec(q) + DIGITS[r .. r+1]
}

function int_to_string_func(n: nat): string
{
  if n == 0 then "0" else int_to_string_rec(n)
}

lemma IntToString_roundtrip(n: nat)
  ensures is_valid_integer(int_to_string_func(n))
  ensures string_to_int_func(int_to_string_func(n)) == n
  decreases n
{
  if n == 0 {
    // int_to_string_func(0) == "0"
    // prove is_valid_integer("0") and string_to_int_func("0") == 0
    assert int_to_string_func(0) == "0";
    assert |int_to_string_func(0)| == 1;
    // the single character is '0' which is in DIGITS
    assert (exists d :: 0 <= d < 10 && DIGITS[d..d+1][0] == int_to_string_func(0)[0]);
    // now string_to_int_func("0") = index_of_digit('0',0) = 0
  } else {
    var q := n / 10;
    var r := n % 10;
    if q != 0 {
      IntToString_roundtrip(q);
      // int_to_string_func(n) == int_to_string_rec(n) == int_to_string_rec(q) + DIGITS[r..r+1]
      assert int_to_string_func(n) == int_to_string_rec(n);
      assert int_to_string_rec(n) == int_to_string_rec(q) + DIGITS[r..r+1];
      // for q != 0, int_to_string_rec(q) == int_to_string_func(q) and is_valid by induction
      assert int_to_string_rec(q) == int_to_string_func(q);
      // therefore concatenation is non-empty and composed of valid digits
      var s := int_to_string_func(n);
      // last character is the digit for r
      assert s[|s|-1] == DIGITS[r..r+1][0];
      // the prefix equals int_to_string_func(q)
      assert s[..|s|-1] == int_to_string_func(q);
      // by induction, prefix is a valid integer string
      assert is_valid_integer(s[..|s|-1]);
      // hence the whole s is a valid integer string
      assert is_valid_integer(s);
      // compute numeric value
      calc {
        string_to_int_func(s);
        = { }
        string_to_int_func(s[..|s|-1]) * 10 + index_of_digit(s[|s|-1], 0);
        = { assert s[..|s|-1] == int_to_string_func(q); }
        string_to_int_func(int_to_string_func(q)) * 10 + index_of_digit(DIGITS[r..r+1][0], 0);
        = { IntToString_roundtrip(q); }
        q * 10 + r;
      }
    } else {
      // q == 0, so n is a single digit r in 1..9
      var s := int_to_string_func(n);
      // int_to_string_rec(0) == "" so s == DIGITS[r..r+1]
      assert int_to_string_func(n) == int_to_string_rec(n);
      assert int_to_string_rec(n) == int_to_string_rec(0) + DIGITS[r..r+1];
      assert int_to_string_rec(0) == "";
      assert s == DIGITS[r..r+1];
      assert |s| == 1;
      assert s[0] == DIGITS[r..r+1][0];
      // is_valid_integer for single digit holds
      assert (exists d :: 0 <= d < 10 && DIGITS[d..d+1][0] == s[0]);
      // and string_to_int_func(s) == index_of_digit(s[0],0) == r == n
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires |stdin_input| > 0
    requires valid_input_format(stdin_input)
    ensures |output| > 0
    ensures output[|output|-1] == '\n'
    ensures is_valid_output(output)
    ensures output_represents_correct_count(stdin_input, output)
// </vc-spec>
// <vc-code>
{
  var lines := split_lines_func(stdin_input);
  var first_line := split_spaces_func(lines[0]);
  var second_line := split_spaces_func(lines[1]);
  var N := string_to_int_func(first_line[0]);
  var A := string_to_int_func(first_line[1]);
  var cards: seq<int> := [];
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant |cards| == i
  {
    cards := cards + [string_to_int_func(second_line[i])];
    i := i + 1;
  }
  var result := count_valid_selections(cards, A);
  assert result >= 0;
  IntToString_roundtrip(result as nat);
  var result_str := int_to_string_func(result as nat);
  output := result_str + "\n";
}
// </vc-code>

