// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>
lemma cube_nonneg(n: nat)
  ensures cube(n) >= 0
{
  assert n >= 0;
  assert n * n >= 0;
  assert cube(n) == n * n * n;
  assert cube(n) >= 0;
}

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
    invariant forall k :: 0 <= k < i ==> cube(k) != n
    decreases n - i + 1
  {
    if cube(i) == n {
      r := true;
      return;
    }
    i := i + 1;
  }
  r := false;
}

// </vc-code>
