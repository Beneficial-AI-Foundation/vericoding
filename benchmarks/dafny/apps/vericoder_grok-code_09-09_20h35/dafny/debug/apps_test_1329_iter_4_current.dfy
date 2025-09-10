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
const primes: seq<int> := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]

function expPrime(N: int, p: int) : int
  requires p > 1 && N >= 0
  decreases N
{
  if N < p then 0 else expPrime(N/p, p) + N/p
}

method count75(N: int) returns (count: int)
  requires ValidInput(N)
  ensures count >= 0
{
  count := 0;
  for i := 0 to |primes|-1
    invariant count >= 0
  {
    if expPrime(N, primes[i]) >= 74 {
      count := count + 1;
    }
  }
}

method count253(N: int) returns (count: int)
  requires ValidInput(N)
  ensures count >= 0
{
  count := 0;
  for i := 0 to |primes|-1
    invariant count >= 0
  {
    var p := primes[i];
    for j := i+1 to |primes|-1 {
      var q := primes[j];
      var ep := expPrime(N, p);
      var eq := expPrime(N, q);
      if ep >= 24 && eq >= 2 {
        count := count + 1;
      }
      if ep >= 2 && eq >= 24 {
        count := count + 1;
      }
    }
  }
}

method count155(N: int) returns (count: int)
  requires ValidInput(N)
  ensures count >= 0
{
  count := 0;
  for i := 0 to |primes|-1
    invariant count >= 0
  {
    var p := primes[i];
    for j := i+1 to |primes|-1 {
      var q := primes[j];
      var ep := expPrime(N, p);
      var eq := expPrime(N, q);
      if ep >= 14 && eq >= 4 {
        count := count + 1;
      }
      if ep >= 4 && eq >= 14 {
        count := count + 1;
      }
    }
  }
}

method count553(N: int) returns (count: int)
  requires ValidInput(N)
  ensures count >= 0
{
  count := 0;
  for i := 0 to |primes|-1
    invariant count >= 0
  {
    var p := primes[i];
    for j := i+1 to |primes|-1 {
      var q := primes[j];
      for k := j+1 to |primes|-1 {
        var r := primes[k];
        var ep := expPrime(N, p);
        var eq := expPrime(N, q);
        var er := expPrime(N, r);
        var da := if ep >= 4 then 1 else 0;
        var db := if eq >= 4 then 1 else 0;
        var dc := if er >= 4 then 1 else 0;
        var dsum := da + db + dc;
        if dsum > 1 && ep >= 2 && eq >= 2 && er >= 2 {
          if dsum == 3 {
            count := count + 3;
          } else {
            count := count + 1;
          }
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
  requires ValidInput(N)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var a := count75(N);
  var b := count253(N);
  var c := count155(N);
  var d := count553(N);
  result := a + b + c + d;
}
// </vc-code>

