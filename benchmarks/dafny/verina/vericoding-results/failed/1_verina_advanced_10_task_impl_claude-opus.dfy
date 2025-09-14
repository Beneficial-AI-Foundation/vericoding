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
/* helper modified by LLM (iteration 5): fixed decreases clause in ComputeExponent */
function ComputeExponent(n: nat, p: nat): nat
    requires p > 1
    decreases n
{
    if n == 0 || n % p != 0 then 0
    else 
        var quotient := n / p;
        if quotient < n then
            1 + ComputeExponent(quotient, p)
        else
            0
}

function BuildPairs(n: nat, primes: seq<nat>, index: nat): seq<(nat, nat)>
    requires forall i :: 0 <= i < |primes| ==> primes[i] > 1
    requires forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
    requires index <= |primes|
    decreases |primes| - index
    ensures forall i :: 0 <= i < |BuildPairs(n, primes, index)| ==> BuildPairs(n, primes, index)[i].0 in primes[index..]
{
    if index >= |primes| then
        []
    else
        var exp := ComputeExponent(n, primes[index]);
        var rest := BuildPairs(n, primes, index + 1);
        [(primes[index], exp)] + rest
}

lemma BuildPairsCorrect(n: nat, primes: seq<nat>, index: nat)
    requires forall i :: 0 <= i < |primes| ==> primes[i] > 1
    requires forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
    requires index <= |primes|
    decreases |primes| - index
    ensures var pairs := BuildPairs(n, primes, index);
            forall i :: 0 <= i < |pairs| ==> pairs[i].0 in primes
{
    if index < |primes| {
        BuildPairsCorrect(n, primes, index + 1);
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
/* code modified by LLM (iteration 5): simplified implementation to avoid timeout */
{
    result := [];
    
    if |primes| == 0 {
        return;
    }
    
    // Build result with all primes, computing exponents
    var i := 0;
    while i < |primes|
        invariant 0 <= i <= |primes|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j].0 == primes[j]
    {
        var exp: nat := 0;
        
        // Only compute exponent if prime is valid
        if primes[i] > 1 {
            var temp := n;
            while temp > 0 && temp % primes[i] == 0
                invariant temp <= n
                decreases temp
            {
                exp := exp + 1;
                temp := temp / primes[i];
            }
        }
        
        result := result + [(primes[i], exp)];
        i := i + 1;
    }
}
// </vc-code>
