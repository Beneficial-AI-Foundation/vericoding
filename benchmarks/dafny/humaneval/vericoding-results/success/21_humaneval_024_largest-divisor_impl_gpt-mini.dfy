// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function is_proper_divisor(n: int, k: int): bool {
  0 < k < n && n % k == 0
}

lemma one_is_divisor(n: int)
  requires n > 1
  ensures n % 1 == 0
{
  assert n % 1 == 0;
}

// </vc-helpers>

// <vc-spec>
method largest_divisor(n: int) returns (d : int)

  requires n > 1

  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
// </vc-spec>
// <vc-code>
{
  var i := n - 1;
  while i > 1 && n % i != 0
    decreases i
    invariant 1 <= i < n
    invariant forall k :: i < k < n ==> n % k != 0
  {
    i := i - 1;
  }
  d := i;
}

// </vc-code>
