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
predicate is_odd(n: int)
{
  n % 2 == 1
}

predicate satisfies_condition(n: int)
  requires n >= 0
{
  n > 10 && is_odd(first_digit(n)) && is_odd(last_digit(n))
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method specialFilter(s: seq<int>) returns (r: seq<int>)
Write a function that takes an array of numbers as input and returns the number of elements in the array that are greater than 10 and both first and last digits of a number are odd (1, 3, 5, 7, 9).
*/
// </vc-description>

// <vc-spec>
method specialFilter(s: seq<int>) returns (r: seq<int>)
  ensures |r| <= |s|
  ensures forall i :: 0 <= i < |r| ==> r[i] in s
  ensures forall i :: 0 <= i < |r| ==> r[i] >= 0 && satisfies_condition(r[i])
  ensures forall x :: x in s && x >= 0 && satisfies_condition(x) ==> x in r
// </vc-spec>
// <vc-code>
{
  r := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |r| <= i
    invariant forall j :: 0 <= j < |r| ==> r[j] in s
    invariant forall j :: 0 <= j < |r| ==> r[j] >= 0 && satisfies_condition(r[j])
    invariant forall k :: 0 <= k < i && s[k] >= 0 && satisfies_condition(s[k]) ==> s[k] in r
  {
    if s[i] >= 0 && satisfies_condition(s[i]) {
      r := r + [s[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
