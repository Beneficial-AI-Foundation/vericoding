predicate ValidInput(N: int)
{
  1 <= N <= 100
}

function countDivisorsWith75Factors(N: int): int
  requires ValidInput(N)
{
  0 // Abstract specification - represents the count of divisors of N! that have exactly 75 divisors
}

predicate ValidOutput(result: int)
{
  result >= 0
}

// <vc-helpers>
function factorialDivisors(n: int): (count: seq<int>)
  decreases n
  requires 1 <= n <= 100
  ensures |count| == n + 1
  ensures forall i :: 1 <= i <= n ==> count[i] >= 0
{
  if n == 1 then [0, 1]
  else
    var prev := factorialDivisors(n - 1);
    var primeFactors := primeFactorization(n);
    var newCount := prev + [0];
    var k := 0;
    while k < |primeFactors|
      invariant 0 <= k <= |primeFactors|
      invariant |newCount| == n + 1
      invariant forall j :: 0 <= j < |newCount| ==> newCount[j] >= 0
    {
      var (p, exp) := primeFactors[k];
      if p < |newCount| then
        newCount := newCount[p := newCount[p] + exp];
      k := k + 1;
    }
    newCount
}

function primeFactorization(n: int): seq<(int, int)>
  requires 2 <= n <= 100
  ensures forall i :: 0 <= i < |result| ==> result[i].0 >= 2 && result[i].1 >= 1
{
  if n == 2 then [(2, 1)]
  else if n % 2 == 0 then
    var rest := primeFactorization(n / 2);
    if |rest| > 0 && rest[0].0 == 2 then
      [(2, rest[0].1 + 1)] + rest[1..]
    else
      [(2, 1)] + rest
  else
    var i := 3;
    while i * i <= n
      invariant i >= 3
      invariant i % 2 == 1
    {
      if n % i == 0 then
        var rest := primeFactorization(n / i);
        if |rest| > 0 && rest[0].0 == i then
          return [(i, rest[0].1 + 1)] + rest[1..];
        else
          return [(i, 1)] + rest;
      i := i + 2;
    }
    [(n, 1)]
}

function countDivisorsFromExponents(exponents: seq<int>): int
  requires forall i :: 0 <= i < |exponents| ==> exponents[i] >= 0
{
  if |exponents| == 0 then 1
  else
    var total := 1;
    var idx := 0;
    while idx < |exponents|
      invariant 0 <= idx <= |exponents|
      invariant total >= 1
    {
      total := total * (exponents[idx] + 1);
      idx := idx + 1;
    }
    total
}

function countValidCombinations(exponents: seq<int>, index: int, current: seq<int>): int
  decreases |exponents| - index
  requires 0 <= index <= |exponents|
  requires |current| == |exponents|
  requires forall i :: 0 <= i < |current| ==> current[i] >= 0
  requires forall i :: index <= i < |exponents| ==> current[i] == 0
{
  if index == |exponents| then
    (if HasExactly75Divisors(current) then 1 else 0)
  else
    var count := 0;
    var maxExp := exponents[index];
    var e := 0;
    while e <= maxExp
      invariant 0 <= e <= maxExp + 1
      invariant count >= 0
    {
      var newCurrent := current;
      newCurrent[index] := e;
      count := count + countValidCombinations(exponents, index + 1, newCurrent);
      e := e + 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
  requires ValidInput(N)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var exponents := factorialDivisors(N);
  var empty := new int[|exponents|];
  var i := 0;
  while i < |empty|
    invariant 0 <= i <= |empty|
    invariant forall j :: 0 <= j < |empty| ==> empty[j] == 0
  {
    empty[i] := 0;
    i := i + 1;
  }
  result := countValidCombinations(exponents, 0, empty);
}
// </vc-code>

