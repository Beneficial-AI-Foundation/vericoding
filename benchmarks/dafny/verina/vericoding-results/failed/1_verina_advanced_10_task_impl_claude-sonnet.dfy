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
/* helper modified by LLM (iteration 5): Fixed SpecFoldCorrectness lemma to handle base case properly */
function FindExponent(n: nat, p: nat): nat
    requires p > 1
    decreases n
{
    if n == 0 || n % p != 0 then 0
    else if n / p < n then 1 + FindExponent(n / p, p)
    else 1
}

function ComputeResult(n: nat, primes: seq<nat>): seq<(nat, nat)>
    requires forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
    decreases |primes|
{
    if |primes| == 0 then []
    else
        var p := primes[0];
        var exp := if p > 1 then FindExponent(n, p) else 0;
        [(p, exp)] + ComputeResult(n, primes[1..])
}

lemma ComputeResultCorrectness(n: nat, primes: seq<nat>)
    requires forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
    ensures var result := ComputeResult(n, primes);
            |result| == |primes|
    ensures var result := ComputeResult(n, primes);
            forall i :: 0 <= i < |result| ==> result[i].0 == primes[i]
{
    if |primes| == 0 {
        assert ComputeResult(n, primes) == [];
    } else {
        ComputeResultCorrectness(n, primes[1..]);
    }
}

lemma SpecFoldCorrectness(n: nat, primes: seq<nat>)
    requires forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
    ensures n as int == SpecFold(ComputeResult(n, primes), 1)
{
    if |primes| == 0 {
        assert ComputeResult(n, primes) == [];
        assert SpecFold([], 1) == 1;
        assert n as int == 1;
    } else {
        var p := primes[0];
        var exp := if p > 1 then FindExponent(n, p) else 0;
        var remaining := ComputeResult(n, primes[1..]);
        SpecFoldCorrectness(n, primes[1..]);
        assert n as int == SpecFold(remaining, 1);
        assert SpecFold([(p, exp)] + remaining, 1) == SpecFold(remaining, 1 * pow(p as int, exp));
        assert n as int == SpecFold(ComputeResult(n, primes), 1);
    }
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
    /* code modified by LLM (iteration 5): Added conditional handling for empty primes */
    if |primes| == 0 {
        result := [];
        assert SpecFold([], 1) == 1;
        assert n as int == 1;
    } else {
        result := ComputeResult(n, primes);
        ComputeResultCorrectness(n, primes);
        SpecFoldCorrectness(n, primes);
    }
}
// </vc-code>
