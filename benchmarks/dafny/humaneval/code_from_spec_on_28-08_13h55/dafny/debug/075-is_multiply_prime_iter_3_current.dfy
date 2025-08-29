function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
function CountPrimeFactors(n: nat, p: nat) : nat
{
    if n <= 1 || p > n then 0
    else if n % p == 0 then 1 + CountPrimeFactors(n / p, p)
    else CountPrimeFactors(n, p + 1)
}

function TotalPrimeFactors(n: nat) : nat
{
    CountPrimeFactors(n, 2)
}

lemma PrimeFactorLemma(n: nat, p: nat)
    requires n > 1 && p >= 2
    ensures CountPrimeFactors(n, p) >= 0
{
}

function GetPrimes(limit: nat) : seq<nat>
{
    seq(limit, i requires 0 <= i < limit => i + 2)
}

predicate IsProductOfExactlyThreePrimes(n: nat)
{
    exists p1, p2, p3 :: Prime(p1) && Prime(p2) && Prime(p3) && n == p1 * p2 * p3
}

function CheckThreePrimeProduct(n: nat, p1: nat, p2: nat, p3: nat) : bool
    requires p1 >= 2 && p2 >= 2 && p3 >= 2
{
    if p1 > n || p2 > n || p3 > n then false
    else if p1 * p2 * p3 > n then false
    else Prime(p1) && Prime(p2) && Prime(p3) && n == p1 * p2 * p3
}

function SearchThreePrimes(n: nat, p1: nat, p2: nat, p3: nat) : bool
    requires p1 >= 2 && p2 >= 2 && p3 >= 2
    decreases n - p1, n - p2, n - p3
{
    if p1 > n || p2 > n || p3 > n then false
    else if p1 * p2 * p3 > n then 
        if p3 < n then SearchThreePrimes(n, p1, p2, p3 + 1)
        else if p2 < n then SearchThreePrimes(n, p1, p2 + 1, 2)
        else if p1 < n then SearchThreePrimes(n, p1 + 1, 2, 2)
        else false
    else if CheckThreePrimeProduct(n, p1, p2, p3) then true
    else if p3 < n then SearchThreePrimes(n, p1, p2, p3 + 1)
    else if p2 < n then SearchThreePrimes(n, p1, p2 + 1, 2)
    else if p1 < n then SearchThreePrimes(n, p1 + 1, 2, 2)
    else false
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_multiply_prime(a: int) -> bool
Write a function that returns true if the given number is the multiplication of 3 prime numbers and false otherwise. Knowing that (a) is less then 100.
*/
// </vc-description>

// <vc-code>
function is_multiply_prime(a: int) : bool
    requires a < 100
    ensures is_multiply_prime(a) <==> (a > 1 && IsProductOfExactlyThreePrimes(a as nat))
{
    if a <= 1 then false
    else SearchThreePrimes(a as nat, 2, 2, 2)
}
// </vc-code>
