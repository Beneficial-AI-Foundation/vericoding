function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
// pure-end
method x_or_y(n: nat, x: int, y: int) returns (result: int)
  // post-conditions-start
  ensures IsPrime(n) ==> result == x
  ensures !IsPrime(n) ==> result == y
  // post-conditions-end
{
  // impl-start
  if IsPrime(n) {
    return x;
  } else {
    return y;
  }
  // impl-end
}
