// <vc-preamble>

predicate is_all_digits(s: string)
{
  forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function count_odd_digits(s: string): int
  requires is_all_digits(s)
  ensures count_odd_digits(s) >= 0
  ensures count_odd_digits(s) <= |s|
{
    if |s| == 0 then 0
    else
        var digit := s[0] as int - '0' as int;
        var is_odd := if digit % 2 == 1 then 1 else 0;
        is_odd + count_odd_digits(s[1..])
}

function int_to_string_func(n: int): string
  requires n >= 0
{
  if n == 0 then "0"
  else int_to_string_rec(n, "")
}

function format_message(count: int): string
  requires count >= 0
{
  var count_str := int_to_string_func(count);
  "the number of odd elements " + count_str + "n the str" + count_str + "ng " + count_str + " of the " + count_str + "nput."
}
function int_to_string_rec(n: int, acc: string): string
  requires n >= 0
  decreases n
{
  if n == 0 then acc
  else
    var digit := n % 10;
    var digit_char := ('0' as int + digit) as char;
    int_to_string_rec(n / 10, [digit_char] + acc)
}

method int_to_string(n: int) returns (s: string)
  requires n >= 0
  ensures s == int_to_string_func(n)
{
    if n == 0 {
        s := "0";
    } else {
        s := "";
        var temp := n;
        while temp > 0
          decreases temp
          invariant temp >= 0
          invariant int_to_string_rec(temp, s) == int_to_string_rec(n, "")
        {
            var digit := temp % 10;
            var digit_char := ('0' as int + digit) as char;
            s := [digit_char] + s;
            temp := temp / 10;
        }
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method odd_count(lst: seq<string>) returns (result: seq<string>)
  requires forall i :: 0 <= i < |lst| ==> is_all_digits(lst[i])
  ensures |result| == |lst|
  ensures forall i :: 0 <= i < |lst| ==> 
    result[i] == format_message(count_odd_digits(lst[i]))
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == format_message(count_odd_digits(lst[j]))
  {
    var count := count_odd_digits(lst[i]);
    var message := format_message(count);
    result := result + [message];
    i := i + 1;
  }
}
// </vc-code>
