function first_digit(n: int): int
  requires n >= 0
  ensures 0 <= first_digit(n) < 10
{
  if n < 10 then n else first_digit(n / 10)
}
// pure-end
function last_digit(n: int): int
  requires n >= 0
  ensures 0 <= last_digit(n) < 10
  ensures last_digit(n) == n % 10
{
  n % 10
}
// pure-end
method specialFilter(s: seq<int>) returns (r: seq<int>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |r| ==> r[i] > 10
  ensures forall x :: x in r ==> x in s
  ensures forall i :: 0 <= i < |r| ==> first_digit(r[i]) % 2 == 1 && last_digit(r[i]) % 2 == 1
  // post-conditions-end
{
  // impl-start
  var i := 0;
  r := [];
  while i < |s|
    // invariants-start
    invariant 0 <= i <= |s|
    invariant forall x :: x in r ==> x in s
    invariant forall i :: 0 <= i < |r| ==> r[i] > 10
    invariant forall x :: x in r ==> x in s
    invariant forall i :: 0 <= i < |r| ==> first_digit(r[i]) % 2 == 1 && last_digit(r[i]) % 2 == 1
    // invariants-end
  {
    if s[i] > 10 && last_digit(s[i]) % 2 == 1 && first_digit(s[i]) % 2 == 1 {
      r := r + [s[i]];
    }
    i := i + 1;
  }
  // impl-end
}
