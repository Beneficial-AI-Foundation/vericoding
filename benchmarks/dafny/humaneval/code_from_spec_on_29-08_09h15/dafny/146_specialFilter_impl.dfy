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
predicate isOdd(n: int)
{
  n % 2 == 1
}

predicate satisfiesCondition(x: int)
{
  x > 10 && isOdd(first_digit(x)) && isOdd(last_digit(x))
}

lemma firstDigitOddEquivalence(x: int)
  requires x >= 0
  ensures isOdd(first_digit(x)) <==> first_digit(x) % 2 == 1
{
}

lemma lastDigitOddEquivalence(x: int)
  requires x >= 0
  ensures isOdd(last_digit(x)) <==> last_digit(x) % 2 == 1
{
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
  // post-conditions-start
  ensures forall i :: 0 <= i < |r| ==> r[i] > 10
  ensures forall x :: x in r ==> x in s
  ensures forall i :: 0 <= i < |r| ==> first_digit(r[i]) % 2 == 1 && last_digit(r[i]) % 2 == 1
  // post-conditions-end
// </vc-spec>

// <vc-code>
{
  r := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < |r| ==> r[j] > 10
    invariant forall x :: x in r ==> x in s
    invariant forall j :: 0 <= j < |r| ==> first_digit(r[j]) % 2 == 1 && last_digit(r[j]) % 2 == 1
  {
    if s[i] > 10 && s[i] >= 0 && first_digit(s[i]) % 2 == 1 && last_digit(s[i]) % 2 == 1 {
      r := r + [s[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

