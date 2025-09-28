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
/* helper modified by LLM (iteration 5): fixed to prevent infinite recursion and division by zero by adding check for n < p */
function GetExponent(n: nat, p: nat): nat
  requires p >= 2
  decreases n
{
  if n < p then 0 else if n % p != 0 then 0 else 1 + GetExponent(n / p, p)
}
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
  /* code modified by LLM (iteration 5): implemented using GetExponent for each prime */
  var i := 0;
  result := [];
  while i < |primes|
  {
    var p := primes[i];
    var exp := 0;
    if p >= 2
    {
      exp := GetExponent(n, p);
    }
    result := result + [(p, exp)];
    i := i + 1;
  }
}
// </vc-code>
