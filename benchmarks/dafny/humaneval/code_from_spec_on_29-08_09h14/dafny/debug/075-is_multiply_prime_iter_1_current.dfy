function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
function factors_of(x: nat) : set<nat>
{
    set k | 1 <= k <= x && x % k == 0
}

function prime_factors_of(x: nat) : set<nat>
{
    set k | k in factors_of(x) && Prime(k)
}

lemma factorization_exists(x: nat)
    requires x > 1
    ensures exists factors: seq<nat> :: 
        |factors| >= 1 && 
        (forall i :: 0 <= i < |factors| ==> Prime(factors[i])) &&
        (forall i :: 0 <= i < |factors| - 1 ==> factors[i] <= factors[i+1]) &&
        x == product(factors)
{
    if Prime(x) {
        var factors := [x];
        assert x == product(factors);
    } else {
        var d := find_smallest_factor(x);
        assert 1 < d < x && x % d == 0;
        factorization_exists(d);
        factorization_exists(x / d);
    }
}

function find_smallest_factor(x: nat) : (d: nat)
    requires x > 1 && !Prime(x)
    ensures 1 < d < x && x % d == 0
{
    var k := 2;
    while k < x
        invariant 2 <= k <= x
        invariant forall j :: 2 <= j < k ==> x % j != 0
    {
        if x % k == 0 {
            return k;
        }
        k := k + 1;
    }
    2
}

function product(factors: seq<nat>) : nat
{
    if |factors| == 0 then 1
    else factors[0] * product(factors[1..])
}

method count_prime_factors(x: nat) returns (count: nat, factors: seq<nat>)
    requires x > 1
    ensures count == |factors|
    ensures forall i :: 0 <= i < |factors| ==> Prime(factors[i])
    ensures x == product(factors)
{
    factors := [];
    var remaining := x;
    count := 0;
    
    var d := 2;
    while remaining > 1
        invariant remaining >= 1
        invariant x == remaining * product(factors)
        invariant forall i :: 0 <= i < |factors| ==> Prime(factors[i])
        invariant count == |factors|
        invariant d >= 2
        decreases remaining
    {
        if remaining % d == 0 {
            if Prime(d) {
                factors := factors + [d];
                count := count + 1;
            }
            remaining := remaining / d;
        } else {
            d := d + 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)
    // pre-conditions-start
    requires x > 1
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    var count, factors := count_prime_factors(x);
    ans := count == 3;
}
// </vc-code>

