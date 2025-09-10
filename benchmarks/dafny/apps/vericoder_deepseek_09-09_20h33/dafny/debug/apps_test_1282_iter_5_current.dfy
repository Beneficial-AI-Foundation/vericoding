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
  ensures forall i :: 0 <= i < |s| ==> reverse(s)[i] == s[|s| - 1 - i]
{
  if |s| == 0 then ""
  else reverse(s[1..]) + [s[0]]
}

function find_char(s: string, c: char, start: int): int
  requires 0 <= start <= |s|
  ensures -1 <= find_char(s, c, start) <= |s|
  ensures find_char(s, c, start) >= start || find_char(s, c, start) == -1
  ensures find_char(s, c, start) != -1 ==> 0 <= find_char(s, c, start) < |s| && s[find_char(s, c, start)] == c
  ensures find_char(s, c, start) != -1 ==> forall i :: start <= i < find_char(s, c, start) ==> s[i] != c
  ensures find_char(s, c, start) == -1 ==> forall i :: start <= i < |s| ==> s[i] != c
  decreases |s| - start
{
  if start >= |s| then -1
  else if s[start] == c then start
  else find_char(s, c, start + 1)
}

function rfind_char(s: string, c: char): int
  ensures -1 <= rfind_char(s, c) < |s|
  ensures rfind_char(s, c) != -1 ==> 0 <= rfind_char(s, c) < |s| && s[rfind_char(s, c)] == c
  ensures rfind_char(s, c) != -1 ==> forall i :: rfind_char(s, c) < i < |s| ==> s[i] != c
  ensures rfind_char(s, c) == -1 ==> forall i :: 0 <= i < |s| ==> s[i] != c
  decreases |s|
{
  if |s| == 0 then -1
  else if s[|s| - 1] == c then |s| - 1
  else rfind_char(s[..|s| - 1], c)
}

function count_char(s: string, c: char): nat
  ensures count_char(s, c) >= 0
  ensures count_char(s, c) == 0 <==> forall i :: 0 <= i < |s| ==> s[i] != c
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + count_char(s[1..], c)
}

function calculate_balance(s: string): int
  ensures calculate_balance(s) >= 0 || calculate_balance(s) < 0
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == 'M' then 1 else -1) + calculate_balance(s[1..])
}

function nat_to_string(n: nat): string
  ensures |nat_to_string(n)| >= 1 || n == 0
{
  if n == 0 then "0" else "1"
}

lemma reverse_reverse(s: string)
  ensures reverse(reverse(s)) == s
{}

lemma count_char_append(s1: string, s2: string, c: char)
  ensures count_char(s1 + s2, c) == count_char(s1, c) + count_char(s2, c)
  decreases |s1|
{
  if |s1| == 0 {
  } else {
    count_char_append(s1[1..], s2, c);
  }
}

lemma calculate_balance_append(s1: string, s2: string)
  ensures calculate_balance(s1 + s2) == calculate_balance(s1) + calculate_balance(s2)
  decreases |s1|
{
  if |s1| == 0 {
  } else {
    calculate_balance_append(s1[1..], s2);
  }
}

lemma time_nonnegative(input: string)
  requires ValidInput(input)
  ensures ComputeSwapTime(input) >= 0
{}
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
  var rev_input := reverse(input);
  var first_f := find_char(rev_input, 'F', 0);
  
  if first_f == -1 {
    result := "0\n";
  } else {
    var first_m_after_f := find_char(rev_input, 'M', first_f + 1);
    if first_m_after_f == -1 {
      result := "0\n";
    } else {
      var last_m := rfind_char(rev_input, 'M');
      if last_m < first_m_after_f {
        result := "0\n";
      } else {
        var substring := rev_input[first_m_after_f..last_m+1];
        var balance := calculate_balance(substring);
        var f_count := count_char(substring, 'F');
        var time: int := balance + f_count + first_m_after_f - first_f - 1;
        if time < 0 {
          result := "0\n";
        } else {
          time_nonnegative(input);
          result := nat_to_string(time as nat) + "\n";
        }
      }
    }
  }
}
// </vc-code>

