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
function reverse(s: seq<char>): seq<char>
  ensures |reverse(s)| == |s|
{
  seq(|s|, i requires 0 <= i < |s| => s[|s|-1-i])
}

function find_char(s: seq<char>, c: char, start: int): int
  requires 0 <= start <= |s|
  ensures result == -1 || (start <= result < |s|)
  decreases |s| - start
{
  if start == |s| then -1
  else if s[start] == c then start
  else find_char(s, c, start+1)
}

function rfind_char(s: seq<char>, c: char): int
  ensures result == -1 || 0 <= result < |s|
  decreases |s|
{
  if |s| == 0 then -1
  else if s[|s|-1] == c then |s|-1
  else rfind_char(s[0..|s|-1], c)
}

function count_char(s: seq<char>, c: char): nat
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == c then 1 + count_char(s[1..], c)
  else count_char(s[1..], c)
}

function calculate_balance(s: seq<char>): nat {
  count_char(s, 'M')
}

function nat_to_string_aux(n: nat, accum: seq<char>): seq<char>
  requires n > 0 ==> forall i :: 0 <= i < |accum| ==> accum[i] >= '0' && accum[i] <= '9'
  decreases n
{
  if n == 0 then accum
  else 
    var digit := (n % 10) as int;
    var ch := ((digit + '0' as int) as char);
    nat_to_string_aux(n / 10, [ch] + accum)
}

function nat_to_string(n: nat): seq<char> {
  if n == 0 then ['0'] else nat_to_string_aux(n, [])
}

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
                lemma NonNegativeExpression(first_m_after_f, first_f, balance, f_count);
                balance + f_count + first_m_after_f - first_f - 1
}

lemma NonNegativeExpression(first_m_after_f: int, first_f: int, balance: nat, f_count: nat)
requires first_f >=0
requires first_m_after_f >= first_f +1
ensures balance + f_count + first_m_after_f - first_f -1 >=0
{
  calculate {
    balance + f_count + first_m_after_f - first_f -1 >= balance + f_count + (first_f +1) - first_f -1 = balance + f_count +1 -1 - (first_f - (first_f +1)) wait no:
    balance + f_count + first_m_after_f - first_f -1 >= balance + f_count + (first_f +1) - first_f -1 = balance + f_count + first_f +1 - first_f -1 = balance + f_count + (first_f - first_f) + (1 -1) = balance + f_count >= balance >=0
  }
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
  var time := ComputeSwapTime(input);
  var str := nat_to_string(time);
  result := str + "\n";
}
// </vc-code>

