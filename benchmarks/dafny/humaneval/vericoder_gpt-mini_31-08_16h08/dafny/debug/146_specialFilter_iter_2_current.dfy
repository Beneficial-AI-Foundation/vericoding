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
// no helpers needed
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
  var res: seq<int> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < |res| ==> (exists j :: 0 <= j < i && res[k] == s[j])
    invariant forall k :: 0 <= k < |res| ==> res[k] > 10 && first_digit(res[k]) % 2 == 1 && last_digit(res[k]) % 2 == 1
  {
    var x := s[i];
    if x > 10 && first_digit(x) % 2 == 1 && last_digit(x) % 2 == 1 {
      res := res + [x];
    }
    i := i + 1;
  }
  r := res;
}
// </vc-code>

