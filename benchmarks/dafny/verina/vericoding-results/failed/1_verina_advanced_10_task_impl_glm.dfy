// <vc-preamble>
function pow(base: int, exp: nat): int
{
    if exp == 0 then 1 else base * pow(base, exp - 1)
}

predicate IsPrime(n: nat)
{
    true // Abstract predicate for prime numbers
}

function SpecFold(pairs: seq<(nat, nat)>, acc: int): int
    decreases |pairs|
{
    if |pairs| == 0 then
        acc
    else
        var p, e := pairs[0].0, pairs[0].1;
        SpecFold(pairs[1..], acc * pow(p as int, e))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindExponents(n: nat, primes: seq<nat>) returns (result: seq<(nat, nat)>)
    requires forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
    ensures n as int == SpecFold(result, 1)
    ensures forall i :: 0 <= i < |result| ==> result[i].0 in primes
    ensures forall p :: p in primes ==> 
        exists j :: 0 <= j < |result| && result[j].0 == p
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fixed tuple access in invariant from [0] to .0 */
  var remaining := n;
  var res: seq<(nat, nat)> := [];
  for i := 0 to |primes| - 1
    invariant 0 <= i <= |primes|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j].0 == primes[j]
    invariant remaining as int * SpecFold(res, 1) == n as int
  {
    var p := primes[i];
    var e := 0;
    while remaining % p == 0
      invariant remaining as int * SpecFold(res, 1) * pow(p as int, e) == n as int
    {
      e := e + 1;
      remaining := remaining / p;
    }
    res := res + [(p, e)];
  }
  result := res;
}
// </vc-code>
