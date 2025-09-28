// <vc-preamble>

predicate is_palindrome(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i]
}

function sum_elements(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum_elements(s[1..])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method will_it_fly(q: seq<int>, w: int) returns (result: bool)
    ensures result == (is_palindrome(q) && sum_elements(q) <= w)
// </vc-spec>
// <vc-code>
{
  var is_pal := true;
  var i := 0;
  while i < |q| / 2
    invariant 0 <= i <= |q| / 2
    invariant is_pal == (forall j :: 0 <= j < i ==> q[j] == q[|q| - 1 - j])
  {
    if q[i] != q[|q| - 1 - i] {
      is_pal := false;
      break;
    }
    i := i + 1;
  }
  
  var sum := sum_elements(q);
  result := is_pal && sum <= w;
}
// </vc-code>
