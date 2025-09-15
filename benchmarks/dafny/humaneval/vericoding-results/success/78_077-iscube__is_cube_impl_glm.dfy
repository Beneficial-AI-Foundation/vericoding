// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_cube(n: nat) returns (r: bool)

  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i <= n
    invariant 0 <= i <= n+1
    invariant forall j :: 0 <= j < i ==> cube(j) != n
  {
    if cube(i) == n {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
