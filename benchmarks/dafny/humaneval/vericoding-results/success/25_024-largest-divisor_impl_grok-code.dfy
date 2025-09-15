// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 2): Fixed duplicate variable name by using 'i' as loop variable and assigning max to 'd' */
  d := 1;
  var i: int := 2;
  while i < n
    invariant 2 <= i <= n
    invariant 1 <= d < i
    invariant n % d == 0
    invariant forall k :: 2 <= k < i && n % k == 0 ==> k <= d
    decreases n - i
  {
    if n % i == 0 {
      d := i;
    }
    i := i + 1;
  }
}
// </vc-code>
