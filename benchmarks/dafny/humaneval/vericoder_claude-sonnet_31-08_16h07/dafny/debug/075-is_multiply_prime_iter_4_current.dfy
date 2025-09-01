function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
lemma PrimeExamples()
    ensures Prime(2) && Prime(3) && Prime(5) && Prime(7) && Prime(11) && Prime(13)
{
}

function Factors(n: nat, limit: nat): set<nat>
    requires limit <= n
{
    set k | 1 <= k <= limit && n % k == 0 :: k
}

lemma FactorsComplete(n: nat)
    requires n > 1
    ensures forall k :: 1 <= k <= n && n % k == 0 <==> k in Factors(n, n)
{
}

function SeqProduct(s: seq<nat>): nat
{
    if |s| == 0 then 1
    else s[0] * SeqProduct(s[1..])
}

lemma SeqProductCorrect(s: seq<nat>)
    requires |s| >= 1
    ensures SeqProduct(s) == s[0] * SeqProduct(s[1..])
{
}

lemma SeqProductPositive(s: seq<nat>)
    requires forall i :: 0 <= i < |s| ==> s[i] > 0
    ensures SeqProduct(s) > 0
{
    if |s| == 0 {
        assert SeqProduct(s) == 1;
    } else {
        SeqProductPositive(s[1..]);
    }
}

lemma SeqProductThree(s: seq<nat>)
    requires |s| == 3
    ensures SeqProduct(s) == s[0] * s[1] * s[2]
{
    calc {
        SeqProduct(s);
        == s[0] * SeqProduct(s[1..]);
        == s[0] * SeqProduct([s[1], s[2]]);
        == s[0] * (s[1] * SeqProduct([s[2]]));
        == s[0] * (s[1] * s[2]);
        == s[0] * s[1] * s[2];
    }
}

method FindFactors(n: nat) returns (factors: seq<nat>)
    requires n > 1
    ensures forall i :: 0 <= i < |factors| ==> factors[i] > 1 && n % factors[i] == 0
    ensures forall i, j :: 0 <= i < j < |factors| ==> factors[i] <= factors[j]
    ensures SeqProduct(factors) == n
    ensures |factors| >= 1
{
    factors := [];
    var temp := n;
    var divisor := 2;
    
    while temp > 1 && divisor * divisor <= temp
        invariant temp >= 1
        invariant divisor >= 2
        invariant temp * SeqProduct(factors) == n
        invariant forall i :: 0 <= i < |factors| ==> factors[i] > 1 && factors[i] < divisor
        invariant forall i, j :: 0 <= i < j < |factors| ==> factors[i] <= factors[j]
        invariant forall i :: 0 <= i < |factors| ==> n % factors[i] == 0
        decreases temp
    {
        if temp % divisor == 0 {
            factors := factors + [divisor];
            temp := temp / divisor;
        } else {
            divisor := divisor + 1;
        }
    }
    
    if temp > 1 {
        factors := factors + [temp];
        assert temp > 1;
        assert n % temp == 0;
    }
    
    // Prove the postconditions
    assert SeqProduct(factors) == n;
    
    // Prove all factors are > 1 and divide n
    forall i | 0 <= i < |factors|
        ensures factors[i] > 1 && n % factors[i] == 0
    {
        if i < |factors| - 1 || temp == 1 {
            // factors[i] was added in the loop
            assert factors[i] > 1;
            assert n % factors[i] == 0;
        } else {
            // factors[i] is temp that was added at the end
            assert factors[i] == temp > 1;
            assert n % factors[i] == 0;
        }
    }
    
    // Prove sorted property
    forall i, j | 0 <= i < j < |factors|
        ensures factors[i] <= factors[j]
    {
        if j < |factors| - 1 || temp == 1 {
            // Both from loop, already proven
        } else {
            // j is the last element (temp)
            if i < |factors| - 1 {
                assert factors[i] < divisor;
                assert temp >= divisor;
                assert factors[i] <= factors[j];
            }
        }
    }
}

method IsPrime(n: nat) returns (result: bool)
    requires n > 1
    ensures result <==> Prime(n)
{
    if n == 2 {
        return true;
    }
    
    var k := 2;
    while k * k <= n
        invariant 2 <= k
        invariant forall j :: 2 <= j < k ==> n % j != 0
    {
        if n % k == 0 {
            assert n % k == 0 && 1 < k < n;
            assert !Prime(n);
            return false;
        }
        k := k + 1;
    }
    
    assert k * k > n;
    assert forall j :: 2 <= j < k ==> n % j != 0;
    
    forall j | 1 < j < n
        ensures n % j != 0
    {
        if j < k {
            assert n % j != 0;
        } else {
            assert j >= k;
            if n % j == 0 {
                var q := n / j;
                assert j * q == n && q >= 1;
                if q == 1 {
                    assert j == n;
                    assert false;
                } else {
                    assert q >= 2;
                    assert 1 < q < n;
                    assert n % q == 0;
                    assert q * j == n;
                    assert q < j;
                    assert q < k;
                    assert n % q != 0;
                    assert false;
                }
            }
        }
    }
    
    return true;
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
    var factors := FindFactors(x);
    
    if |factors| != 3 {
        if |factors| == 3 {
            assert false;
        }
        // If not exactly 3 factors, then not a product of 3 primes
        return false;
    }
    
    var prime1 := IsPrime(factors[0]);
    var prime2 := IsPrime(factors[1]);
    var prime3 := IsPrime(factors[2]);
    
    if prime1 && prime2 && prime3 {
        assert Prime(factors[0]) && Prime(factors[1]) && Prime(factors[2]);
        assert SeqProduct(factors) == x;
        SeqProductThree(factors);
        assert x == factors[0] * factors[1] * factors[2];
        return true;
    }
    
    return false;
}
// </vc-code>

