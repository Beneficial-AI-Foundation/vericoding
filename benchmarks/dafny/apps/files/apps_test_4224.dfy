Given an array of positive integers, find the maximum number of operations possible where each operation
allows dividing elements by 2 (if even) or multiplying by 3, with at least one division by 2 required per operation.

predicate ValidInput(a: seq<int>) {
  forall i :: 0 <= i < |a| ==> a[i] > 0
}

function CountFactorsOfTwo(n: int): int
  requires n > 0
  decreases n
{
  if n % 2 == 0 then 1 + CountFactorsOfTwo(n / 2)
  else 0
}

function SumFactors(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  requires forall j :: 0 <= j < |a| ==> a[j] > 0
  decreases |a| - i
{
  if i == |a| then 0
  else CountFactorsOfTwo(a[i]) + SumFactors(a, i + 1)
}

function MaxOperations(a: seq<int>): int
  requires ValidInput(a)
{
  SumFactors(a, 0)
}

function power(base: int, exp: int): int
  requires base >= 0
  requires exp >= 0
{
  if exp == 0 then 1
  else base * power(base, exp - 1)
}

method solve(a: seq<int>) returns (result: int)
  requires ValidInput(a)
  ensures result >= 0
  ensures result == MaxOperations(a)
{
  result := 0;
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant result >= 0
    invariant result == SumFactors(a, 0) - SumFactors(a, i)
  {
    var num := a[i];
    var count := 0;
    while num % 2 == 0
      invariant num > 0
      invariant count >= 0
      invariant a[i] == num * power(2, count)
      invariant CountFactorsOfTwo(a[i]) == count + CountFactorsOfTwo(num)
      decreases num
    {
      num := num / 2;
      count := count + 1;
    }
    result := result + count;
  }
}
