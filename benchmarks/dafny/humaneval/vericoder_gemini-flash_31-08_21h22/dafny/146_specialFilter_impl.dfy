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
function first_digit_is_odd(n: int): bool
  requires n >= 0
{
  first_digit(n) % 2 == 1
}

function last_digit_is_odd(n: int): bool
  requires n >= 0
{
  last_digit(n) % 2 == 1
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
  var result: seq<int> := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < |result| ==> result[j] > 10
    invariant forall j :: 0 <= j < |result| ==> result[j] in s
    invariant forall j :: 0 <= j < |result| ==> first_digit(result[j]) % 2 == 1 && last_digit(result[j]) % 2 == 1
    invariant forall j :: 0 <= j < |result| ==> exists k :: 0 <= k < i && result[j] == s[k]
  {
    if i < |s| { // Add this check to prevent out-of-bounds access
      var x := s[i];
      if x > 10 && first_digit(x) % 2 == 1 && last_digit(x) % 2 == 1 {
        result := result + [x];
      }
    }
  }
  return result;
}
// </vc-code>

