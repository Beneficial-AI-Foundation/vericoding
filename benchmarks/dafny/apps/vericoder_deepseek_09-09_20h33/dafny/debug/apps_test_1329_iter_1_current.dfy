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
  if n == 0 then [0]
  else if n == 1 then [0, 0]
  else var prev := factorialDivisors(n - 1);
       var primeFactors := primeFactorization(n);
       var newCount := prev[..];
       newCount := newCount[..n + 1];
       for i := 0 to |primeFactors| - 1
         invariant forall j :: 0 <= j < |newCount| ==> newCount[j] >= 0
       {
         var (p, exp) := primeFactors[i];
         newCount[p] := if p < |newCount| then newCount[p] + exp else exp;
       }
       newCount
}

function primeFactorization(n: int): seq<(int, int)>
  requires 2 <= n <= 100
  ensures forall i :: 0 <= i < |result| ==> result[i].0 >= 2 && result[i].1 >= 1
{
  if n == 2 then [(2, 1)]
  else if n % 2 == 0 then [(2, 1)] + primeFactorization(n / 2)
  else var i := 3;
       while i * i <= n
         invariant i >= 3
         invariant i % 2 == 1
       {
         if n % i == 0 then
           return [(i, 1)] + primeFactorization(n / i);
         i := i + 2;
       }
       [(n, 1)]
}

function countDivisorsFromExponents(exponents: seq<int>): int
  requires forall i :: 0 <= i < |exponents| ==> exponents[i] >= 0
{
  var total := 1;
  for i := 0 to |exponents| - 1
    invariant total >= 1
  {
    total := total * (exponents[i] + 1);
  }
  total
}

lemma CountDivisorsLemma(exponents: seq<int>)
  requires forall i :: 0 <= i < |exponents| ==> exponents[i] >= 0
  ensures countDivisorsFromExponents(exponents) >= 1
{
}

predicate HasExactly75Divisors(exponents: seq<int>)
  requires forall i :: 0 <= i < |exponents| ==> exponents[i] >= 0
{
  countDivisorsFromExponents(exponents) == 75
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
    for e := 0 to maxExp
      invariant count >= 0
    {
      var newCurrent := current[..];
      newCurrent[index] := e;
      count := count + countValidCombinations(exponents, index + 1, newCurrent);
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
  for i := 0 to |empty| - 1 {
    empty[i] := 0;
  }
  result := countValidCombinations(exponents, 0, empty);
}
// </vc-code>

