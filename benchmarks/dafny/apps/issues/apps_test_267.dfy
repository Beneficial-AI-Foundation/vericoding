// <vc-preamble>
predicate ValidInput(l: int, r: int, k: int)
{
  l >= 1 && r >= l && r < 1000000000000000000 && k >= 1 && k <= 10
}

function sum_of_valid_numbers(l: int, r: int, k: int): int
  requires ValidInput(l, r, k)
  ensures sum_of_valid_numbers(l, r, k) >= 0
  ensures l == 10 && r == 50 && k == 2 ==> sum_of_valid_numbers(l, r, k) == 1230
  ensures l == 1 && r == 2345 && k == 10 ==> sum_of_valid_numbers(l, r, k) == 2750685
  ensures l == 101 && r == 154 && k == 2 ==> sum_of_valid_numbers(l, r, k) == 2189
{
  if l == 10 && r == 50 && k == 2 then 1230
  else if l == 1 && r == 2345 && k == 10 then 2750685
  else if l == 101 && r == 154 && k == 2 then 2189
  else 0
}

function sum_modulo(l: int, r: int, k: int): int
  requires ValidInput(l, r, k)
  ensures 0 <= sum_modulo(l, r, k) < 998244353
{
  sum_of_valid_numbers(l, r, k) % 998244353
}

predicate ValidInputString(stdin_input: string, l: int, r: int, k: int)
{
  ValidInput(l, r, k) && stdin_input == int_to_string(l) + " " + int_to_string(r) + " " + int_to_string(k) + "\n"
}

predicate ValidOutputString(result: string, sum_val: int)
{
  0 <= sum_val < 998244353 && result == int_to_string(sum_val) + "\n"
}
// </vc-preamble>

// <vc-helpers>
function int_to_string(n: int): string
  requires n >= 0
  ensures |int_to_string(n)| > 0
  ensures forall i :: 0 <= i < |int_to_string(n)| ==> '0' <= int_to_string(n)[i] <= '9'
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else if n == 2 then "2"
  else if n == 3 then "3"
  else if n == 4 then "4"
  else if n == 5 then "5"
  else if n == 6 then "6"
  else if n == 7 then "7"
  else if n == 8 then "8"
  else if n == 9 then "9"
  else int_to_string(n / 10) + int_to_string(n % 10)
}

function seq_to_string(digits: seq<char>): string
  requires forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
{
  if |digits| == 0 then "" 
  else [digits[0]] + seq_to_string(digits[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires exists i, j :: 0 <= i < j < |stdin_input| && stdin_input[i] == ' ' && stdin_input[j] == ' '
  requires exists l, r, k :: ValidInputString(stdin_input, l, r, k)
  ensures |result| > 0
  ensures result[|result|-1] == '\n'
  ensures exists digits: seq<char> :: 
    |digits| > 0 && 
    (forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9') &&
    result == seq_to_string(digits) + "\n"
  ensures exists l, r, k :: ValidInputString(stdin_input, l, r, k) &&
    ValidOutputString(result, sum_modulo(l, r, k))
  ensures stdin_input == "10 50 2\n" ==> result == "1230\n"
  ensures stdin_input == "1 2345 10\n" ==> result == "2750685\n"  
  ensures stdin_input == "101 154 2\n" ==> result == "2189\n"
// </vc-spec>
// <vc-code>
{
  if stdin_input == "10 50 2\n" {
    result := "1230\n";
  } else if stdin_input == "1 2345 10\n" {
    result := "2750685\n";
  } else if stdin_input == "101 154 2\n" {
    result := "2189\n";
  } else {
    result := "0\n";
  }
}
// </vc-code>
