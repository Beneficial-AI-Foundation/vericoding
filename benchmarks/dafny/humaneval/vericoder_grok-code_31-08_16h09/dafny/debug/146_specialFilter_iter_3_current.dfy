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
// <vc-helpers>
// </vc-helpers>
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
  var r: seq<int> := [];
  for i := 0 to |s| - 1 {
    var x := s[i];
    if x > 10 && first_digit(x) % 2 == 1 && last_digit(x) % 2 == 1 {
      r := r + [x];
    }
  }
}
// </vc-code>

