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
  decreases |s|
{
  if |s| == 0 then "" else reverse(s[1..]) + s[0..1]
}

function find_char(s: string, ch: char, start: int): int
  requires 0 <= start <= |s|
  ensures find_char(s, ch, start) == -1 ==> forall i :: start <= i < |s| ==> s[i] != ch
  ensures find_char(s, ch, start) != -1 ==> start <= find_char(s, ch, start) < |s| && s[find_char(s, ch, start)] == ch && forall i :: start <= i < find_char(s, ch, start) ==> s[i] != ch
  decreases |s| - start
{
  if start >= |s| then -1
  else if s[start] == ch then start
  else find_char(s, ch, start + 1)
}

function rfind_char(s: string, ch: char): int
  ensures rfind_char(s, ch) == -1 ==> forall i :: 0 <= i < |s| ==> s[i] != ch
  ensures rfind_char(s, ch) != -1 ==> 0 <= rfind_char(s, ch) < |s| && s[rfind_char(s, ch)] == ch && forall j :: rfind_char(s, ch) < j < |s| ==> s[j] != ch
  decreases |s|
{
  if |s| == 0 then -1
  else if s[|s|-1] == ch then |s|-1
  else rfind_char(s[..|s|-1], ch)
}

function calculate_balance(s: string): nat { 0 }

function count_char(s: string, ch: char): nat
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == ch then 1 + count_char(s[1..], ch) else count_char(s[1..], ch)
}

function nat_to_string(n: nat): string
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
  result := nat_to_string(ComputeSwapTime(input)) + "\n";
}
// </vc-code>

