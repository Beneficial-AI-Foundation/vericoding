// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
predicate IsSpecial(x: int) { x >= 0 && x > 10 && first_digit(x) % 2 == 1 && last_digit(x) % 2 == 1 }
// </vc-helpers>

// <vc-spec>
method specialFilter(s: seq<int>) returns (r: seq<int>)

  ensures forall i :: 0 <= i < |r| ==> r[i] > 10
  ensures forall x :: x in r ==> x in s
  ensures forall i :: 0 <= i < |r| ==> first_digit(r[i]) % 2 == 1 && last_digit(r[i]) % 2 == 1
// </vc-spec>
// <vc-code>
{
  var i := 0;
  r := [];
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < |r| ==> r[j] > 10
    invariant forall j :: 0 <= j < |r| ==> first_digit(r[j]) % 2 == 1 && last_digit(r[j]) % 2 == 1
    invariant forall x :: x in r ==> x in s
    decreases |s| - i
  {
    var x := s[i];
    if x >= 0 && x > 10 && first_digit(x) % 2 == 1 && last_digit(x) % 2 == 1 {
      r := r + [x];
    }
    i := i + 1;
  }
}
// </vc-code>
