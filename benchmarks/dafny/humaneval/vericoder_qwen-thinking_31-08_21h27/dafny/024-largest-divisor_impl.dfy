

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method largest_divisor(n: int) returns (d : int)
  // pre-conditions-start
  requires n > 1
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
var k := 2;
while (k * k <= n) {
    invariant 2 <= k
    invariant forall i :: 2 <= i < k ==> n % i != 0
    variant n - k
    if n % k == 0 {
        return n / k;
    }
    k := k + 1;
}
return 1;
// </vc-code>

