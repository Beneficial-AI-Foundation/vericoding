function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
predicate IsComposite(n: nat)
  requires n > 1
{
  exists k :: 2 <= k < n && n % k == 0
}

lemma PrimeOrComposite(n: nat)
  requires n > 1
  ensures IsPrime(n) || IsComposite(n)
{
}

lemma NotPrimeImpliesComposite(n: nat)
  requires n > 1
  ensures !IsPrime(n) ==> IsComposite(n)
{
  PrimeOrComposite(n);
}

lemma PrimeNotComposite(n: nat)
  requires n > 1
  ensures IsPrime(n) <==> !IsComposite(n)
{
  if IsPrime(n) {
    assert forall k :: 2 <= k < n ==> n % k != 0;
    assert !(exists k :: 2 <= k < n && n % k == 0);
  } else {
    NotPrimeImpliesComposite(n);
  }
}
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
  if n <= 1 {
    result := y;
  } else if n == 2 {
    result := x;
  } else {
    var i := 2;
    while i < n
      invariant 2 <= i <= n
      invariant forall k :: 2 <= k < i ==> n % k != 0
    {
      if n % i == 0 {
        // We found a divisor, so n is not prime
        result := y;
        return;
      }
      i := i + 1;
    }
    // If we got here, no divisors were found
    result := x;
  }
}
// </vc-code>

