predicate ValidInput(input: string)
{
    |input| >= 1 && forall i :: 0 <= i < |input| ==> input[i] == 'M' || input[i] == 'F'
}

function ComputeSwapTime(input: string): nat
    requires ValidInput(input)
{
    var rev_input := reverse(input);
    var first_f := find_char(rev_input, 'F', 0);

    if first_f == -1 then 0
    else
        var first_m_after_f := find_char(rev_input, 'M', first_f + 1);
        if first_m_after_f == -1 then 0
        else
            var last_m := rfind_char(rev_input, 'M');
            if last_m < first_m_after_f then 0
            else
                var substring := rev_input[first_m_after_f..last_m+1];
                var balance := calculate_balance(substring);
                var f_count := count_char(substring, 'F');
                balance + f_count + first_m_after_f - first_f - 1
}

// <vc-helpers>
function reverse(s: string): string
  ensures |reverse(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> reverse(s)[i] == s[|s|-1-i]
{
  if |s| == 0 then ""
  else reverse(s[1..]) + s[0..1]
}

function find_char(s: string, c: char, start_index: nat): int
  requires 0 <= start_index <= |s|
  ensures -1 <= find_char(s, c, start_index) < |s|
  ensures find_char(s, c, start_index) == -1 || s[find_char(s, c, start_index)] == c
  ensures find_char(s, c, start_index) == -1 || forall i :: start_index <= i < find_char(s, c, start_index) ==> s[i] != c
{
  var i := start_index;
  while i < |s|
    invariant start_index <= i <= |s|
    invariant forall k :: start_index <= k < i ==> s[k] != c
  {
    if s[i] == c then return i;
    i := i + 1;
  }
  return -1;
}

function rfind_char(s: string, c: char): int
  ensures -1 <= rfind_char(s, c) < |s|
  ensures rfind_char(s, c) == -1 || s[rfind_char(s, c)] == c
  ensures rfind_char(s, c) == -1 || forall i :: rfind_char(s, c) < i < |s| ==> s[i] != c
{
  var i := |s| - 1;
  while i >= 0
    invariant -1 <= i < |s|
    invariant forall k :: i < k < |s| ==> s[k] != c
  {
    if s[i] == c then return i;
    i := i - 1;
  }
  return -1;
}

function calculate_balance(s: string): int
  ensures calculate_balance(s) >= 0
  ensures calculate_balance(s) <= |s|
{
  var m_count := 0;
  var f_count := 0;
  var balance := 0;
  var max_balance := 0 as int; // Changed to int explicitly

  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant m_count == count_char(s[0..i], 'M')
    invariant f_count == count_char(s[0..i], 'F')
    invariant balance == m_count - f_count
    invariant max_balance == MaxBalance(s[0..i])
  {
    if s[i] == 'M' then
      m_count := m_count + 1;
    else
      f_count := f_count + 1;
    balance := m_count - f_count;
    if balance > max_balance then
      max_balance := balance;
    i := i + 1;
  }
  return max_balance;
}

function count_char(s: string, c: char): nat
  ensures 0 <= count_char(s, c) <= |s|
{
  var count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == count_char_prefix(s, c, i)
  {
    if s[i] == c then
      count := count + 1;
    i := i + 1;
  }
  return count;
}

function count_char_prefix(s: string, c: char, len: nat): nat
  requires 0 <= len <= |s|
  Ensures 0 <= count_char_prefix(s, c, len) <= len
{
  if len == 0 then 0
  else (if s[len-1] == c then 1 else 0) + count_char_prefix(s, c, len - 1)
}

function MaxBalance(s: string): nat
  ensures MaxBalance(s) <= |s|
{
  if |s| == 0 then 0
  else
    var balance_so_far := (count_char(s, 'M') as int) - (count_char(s, 'F') as int);
    (Max(MaxBalance(s[0..|s|-1]) as int, balance_so_far)) as nat // Adjusted type for Max
}

function Max(a: int, b: int): int
{
  if a > b then a else b
}

function nat_to_string(n: nat): string
{
  if n == 0 then "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant (temp > 0 ==> s != "") || (n == 0 && s == "") || (n > 0 && temp < n && s != "")
      // Fix: (temp % 10 as char) is incorrect, it should be the result of nat_to_char.
      // Also, no need to prove (temp % 10 as char).IsDigit() as it's handled by nat_to_char postcondition.
      invariant (temp > 0 ==> (temp/10)*10 + (temp%10) == temp)
    {
      s := (nat_to_char(temp % 10)) + s;
      temp := temp / 10;
    }
    s
}

function nat_to_char(n: nat): char
  requires 0 <= n <= 9
  ensures ('0' <= nat_to_char(n) <= '9')
{
  ('0' + n as char) // (n as char) + '0' is not valid, it should be ('0' + n) or Char.FromInt('0' as int + n)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| >= 1
    ensures result[|result|-1] == '\n'
    ensures exists val :: val >= 0 && result == nat_to_string(val) + "\n"
    ensures result == nat_to_string(ComputeSwapTime(input)) + "\n"
// </vc-spec>
// <vc-code>
{
  var swap_time := ComputeSwapTime(input);
  result := nat_to_string(swap_time) + "\n";
}
// </vc-code>

