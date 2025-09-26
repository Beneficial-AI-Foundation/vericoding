// <vc-preamble>
predicate isPrime(n: int)
{
  n >= 2 && (forall k :: 2 <= k < n ==> n % k != 0)
}

predicate ValidInput(X: int)
{
  2 <= X <= 100000
}

predicate ValidOutput(X: int, result: int)
{
  result >= X && isPrime(result) && (forall p :: X <= p < result ==> !isPrime(p))
}
// </vc-preamble>

// <vc-helpers>
method isPrimeCheck(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> isPrime(n)
{
  if n == 2 {
    return true;
  }
  if n % 2 == 0 {
    return false;
  }

  var i := 3;
  while i * i <= n
    invariant i >= 3 && i % 2 == 1
    invariant n % 2 != 0
    invariant (forall k :: 2 <= k < i ==> n % k != 0)
  {
    if n % i == 0 {
      return false;
    }
    i := i + 2;
  }

  assert i * i > n;
  assert (forall k :: 2 <= k < i ==> n % k != 0);
  assert (forall k :: i <= k < n ==> (n % k != 0));

  return true;
}
// </vc-helpers>

// <vc-spec>
method solve(X: int) returns (result: int)
  requires ValidInput(X)
  ensures ValidOutput(X, result)
// </vc-spec>
// <vc-code>
{
  var candidate := X;
  while candidate <= 1299827
    invariant candidate >= X
    invariant forall p :: X <= p < candidate ==> !isPrime(p)
  {
    var prime := isPrimeCheck(candidate);
    if prime {
      return candidate;
    }
    candidate := candidate + 1;
  }

  result := 1299827;
  assert isPrime(1299827);

  return result;
}
// </vc-code>
