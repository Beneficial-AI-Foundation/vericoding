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
// No helper lemmas required for this solution.
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
  requires ValidInput(N)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var c2 := 0;
  var c4 := 0;
  var c14 := 0;
  var c24 := 0;
  var c74 := 0;

  var p := 2;
  while p <= N
    invariant 2 <= p <= N+1
    invariant 0 <= c2 <= p
    invariant 0 <= c4 <= p
    invariant 0 <= c14 <= p
    invariant 0 <= c24 <= p
    invariant 0 <= c74 <= p
    decreases N + 1 - p
  {
    var isPrime := true;
    var d := 2;
    while d * d <= p
      invariant 2 <= d <= p
      decreases p - d
    {
      if p % d == 0 {
        isPrime := false;
        break;
      }
      d := d + 1;
    }

    if isPrime {
      var e := 0;
      var pow := p;
      while pow <= N
        invariant pow >= 1
        decreases N - pow
      {
        e := e + N / pow;
        pow := pow * p;
      }

      if e >= 2 { c2 := c2 + 1; }
      if e >= 4 { c4 := c4 + 1; }
      if e >= 14 { c14 := c14 + 1; }
      if e >= 24 { c24 := c24 + 1; }
      if e >= 74 { c74 := c74 + 1; }
    }

    p := p + 1;
  }

  var term1 := c74;
  var term2 := if c2 >= 1 then c24 * (c2 - 1) else 0;
  var term3 := if c4 >= 1 then c14 * (c4 - 1) else 0;
  var term4 := 0;
  if c4 >= 2 && c2 >= 2 {
    term4 := (c4 * (c4 - 1) / 2) * (c2 - 2);
  } else {
    term4 := 0;
  }

  result := term1 + term2 + term3 + term4;
}
// </vc-code>

