function first_digit(n: int): int
  requires n >= 0
  ensures 0 <= first_digit(n) < 10
{
  if n < 10 then n else first_digit(n / 10)
}
function last_digit(n: int): int
  requires n >= 0
  ensures 0 <= last_digit(n) < 10
  ensures last_digit(n) == n % 10
{
  n % 10
}

// <vc-helpers>
function first_digit_func(n: int): int
  requires n >= 0
  ensures 0 <= first_digit_func(n) < 10
{
  if n < 10 then n else first_digit_func(n / 10)
}
function last_digit_func(n: int): int
  requires n >= 0
  ensures 0 <= last_digit_func(n) < 10
  ensures last_digit_func(n) == n % 10
{
  n % 10
}
// </vc-helpers>

// <vc-spec>
method specialFilter(s: seq<int>) returns (r: seq<int>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |r| ==> r[i] > 10
  ensures forall x :: x in r ==> x in s
  ensures forall i :: 0 <= i < |r| ==> first_digit(r[i]) % 2 == 1 && last_digit(r[i]) % 2 == 1
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var r_temp: seq<int> := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < |r_temp| ==> r_temp[j] > 10
    invariant forall x :: x in r_temp ==> x in s[..i]
    invariant forall j :: 0 <= j < |r_temp| ==> first_digit(r_temp[j]) % 2 == 1 && last_digit(r_temp[j]) % 2 == 1
  {
    if i < |s| { // Ensure i is a valid index
      var x := s[i];
      if x > 10 && first_digit(x) % 2 == 1 && last_digit(x) % 2 == 1 {
        r_temp := r_temp + [x];
      }
    }
  }
  return r_temp;
}
// </vc-code>

