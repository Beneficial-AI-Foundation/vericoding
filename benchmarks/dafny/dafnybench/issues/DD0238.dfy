// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
function even(n: int): bool
  requires n >= 0
// </vc-spec>
// <vc-code>
{
  if n == 0 then true else !even(n-1)
}
// </vc-code>

method is_even(n: int) returns (r: bool)
  requires n >= 0;
  ensures r <==> even(n);
{
  var i: int := 0;
  r := true;

  while i < n
    invariant 0 <= i <= n;
    invariant r <==> even(i);
  {
    r := !r;
    i := i + 1;
  }
}