//ATOM divides
predicate divides(a: int, b: int)
  requires a != 0
{
  b % a == 0
}

//ATOM IsPrime
predicate IsPrime(n: int)
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

//IMPL Main
method Main()
{
}