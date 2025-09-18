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
  /* code modified by LLM (iteration 5): Fixed compilation error in invariant. */
  result := [];
  var temp_n := n;
  for i := 0 to |primes|
    invariant 0 <= i <= |primes|
    invariant n as int == SpecFold(result, 1) * temp_n as int * (if i < |primes| then SpecFold([(primes[k], 0) | k := i..|primes|-1 ], 1) else 1)
    invariant forall k :: 0 <= k < |result| ==> result[k].0 in primes
    invariant temp_n >= 0
    invariant (forall k :: 0 <= k < i ==> (exists entry_idx :: 0 <= entry_idx < |result| && result[entry_idx].0 == primes[k]))
  {
    var p := primes[i];
    var exponent := 0;
    while temp_n > 0 && temp_n % p == 0
      invariant temp_n >= 0
      invariant exponent >= 0
      invariant n as int == SpecFold(result, 1) * (temp_n * pow(p as int, exponent)) as int * (if i < |primes| then SpecFold([(primes[k], 0) | k := i..|primes|-1 ], 1) else 1)
      invariant forall k :: 0 <= k < |result| ==> result[k].0 in primes
      decreases temp_n
    {
      temp_n := temp_n / p;
      exponent := exponent + 1;
    }
    if exponent > 0 {
      result := result + [(p, exponent)];
    }
  }
}
// </vc-code>
