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
lemma FilterPreservesElements(s: seq<int>, r: seq<int>)
  ensures forall x :: x in r ==> x in s
{
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
method SpecialFilter(s: seq<int>) returns (r: seq<int>)
  ensures forall i :: 0 <= i < |r| ==> r[i] > 10
  ensures forall x :: x in r ==> x in s
  ensures forall i :: 0 <= i < |r| ==> first_digit(r[i]) % 2 == 1 && last_digit(r[i]) % 2 == 1
{
  r := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < |r| ==> r[k] > 10
    invariant forall k :: 0 <= k < |r| ==> first_digit(r[k]) % 2 == 1 && last_digit(r[k]) % 2 == 1
    invariant forall x :: x in r ==> exists j :: 0 <= j < i && s[j] == x
  {
    if s[i] > 10 && first_digit(s[i]) % 2 == 1 && last_digit(s[i]) % 2 == 1
    {
      r := r + [s[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
