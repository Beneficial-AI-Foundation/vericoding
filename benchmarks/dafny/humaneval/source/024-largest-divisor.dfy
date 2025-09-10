method largest_divisor(n: int) returns (d : int)
  // pre-conditions-start
  requires n > 1
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
  // post-conditions-end
{
    // impl-start
    d := n - 1;
    while (d >= 1)
        // invariants-start
        invariant 1 <= d < n
        invariant forall k :: d < k < n ==> n % k != 0
        // invariants-end
    {
        if (n % d == 0) {
            return d;
        }
        d := d - 1;
    }
    return 1;
    // impl-end
}
