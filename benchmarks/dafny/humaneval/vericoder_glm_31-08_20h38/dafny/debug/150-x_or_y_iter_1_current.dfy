function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method x_or_y(n: nat, x: int, y: int) returns (result: int)
  // post-conditions-start
  ensures IsPrime(n) ==> result == x
  ensures !IsPrime(n) ==> result == y
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if IsPrime(n) then x else y
}
// </vc-code>

