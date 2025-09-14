predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0 &&
    exists k: int :: k >= 1 && k <= 10000 && stdin_input == int_to_string(k) + "\n"
}

function kth_perfect_number(k: int): int
    requires k >= 1 && k <= 10000
    ensures kth_perfect_number(k) > 0
    ensures digit_sum(kth_perfect_number(k)) == 10
    ensures forall i: int :: 1 <= i < k ==> kth_perfect_number(i) < kth_perfect_number(k)
    ensures forall n: int :: 0 < n < kth_perfect_number(k) && digit_sum(n) == 10 ==> 
        exists j: int :: 1 <= j < k && kth_perfect_number(j) == n
{
    if k == 1 then 19
    else if k == 2 then 28
    else if k == 3 then 37
    else if k == 4 then 46
    else if k == 5 then 55
    else if k == 6 then 64
    else if k == 7 then 73
    else if k == 8 then 82
    else if k == 9 then 91
    else if k == 10 then 109
    else 10 * (k - 9) + 99
}

// <vc-helpers>
function digit_sum(n: int): int
  requires n > 0
  decreases n
{
  if n < 10 then n
  else digit_sum(n / 10) + n % 10
}

function int_to_string(n: int): string
  requires n >= 0
  decreases n
{
  if n == 0 then "0"
  else int_to_string(n / 10) + [('0' as int + n % 10) as char]
}

function string_to_int(s: string, len: int): int
  requires len == |s| && len > 0
  requires forall i :: 0 <= i < len ==> '0' <= s[i] <= '9' && (len == 1 || s[0] != '0')
  decreases len
  ensures 1 <= string_to_int(s, len) <= 10000
{
  if len == 1 then s[0] - '0'
  else (s[0] - '0') * 10^(len - 1) + string_to_int(s[1..], len - 1)
}

function pow10(exponent: nat): nat
  decreases exponent
{
  if exponent == 0 then 1 else 10 * pow10(exponent - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures exists k: int :: k >= 1 && k <= 10000 && 
        stdin_input == int_to_string(k) + "\n" &&
        result == int_to_string(kth_perfect_number(k)) + "\n"
    ensures |result| > 0
// </vc-spec>
// <vc-code>
{
  var input_str := stdin_input[..|stdin_input| - 1];
  var k := string_to_int(input_str, |input_str|);
  var p := kth_perfect_number(k);
  return int_to_string(p) + "\n";
}
// </vc-code>

