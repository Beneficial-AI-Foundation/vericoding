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
lemma FirstDigitNonNegative(n: int)
  requires n >= 0
  ensures first_digit(n) >= 0
{
  // Follows from the ensures clause of first_digit
}

lemma LastDigitNonNegative(n: int)
  requires n >= 0
  ensures last_digit(n) >= 0
{
  // Follows from the ensures clause of last_digit
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
  r := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < |r| ==> r[j] > 10
    invariant forall x :: x in r ==> x in s[0..i]
    invariant forall x :: x in r ==> x in s
    invariant forall j :: 0 <= j < |r| ==> first_digit(r[j]) % 2 == 1 && last_digit(r[j]) % 2 == 1
  {
    if s[i] > 10 && first_digit(s[i]) % 2 == 1 && last_digit(s[i]) % 2 == 1 {
      r := r + [s[i]];
    }
  }
}
// </vc-code>

