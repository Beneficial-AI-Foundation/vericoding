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
        invariant 2 <= k <= n + 1
        invariant forall j :: 2 <= j < k ==> n % j != 0
        decreases n - k
    {
        if n % k == 0 {
            return false;
        }
        k := k + 1;
    }
    
    assert forall j {:trigger n % j} :: 2 <= j < k ==> n % j != 0;
    assert k * k > n;
    
    forall j | 2 <= j < n
        ensures n % j != 0
    {
        if j < k {
            assert n % j != 0;
        } else {
            assert j >= k;
            assert j * j >= k * k > n;
            if n % j == 0 {
                assert j * (n / j) == n;
                assert n / j >= 1;
                if n / j == 1 {
                    assert j == n;
                    assert false;
                } else {
                    assert n / j >= 2;
                    assert j * (n / j) >= j * 2 >= k * 2;
                    assert k >= 2;
                    assert j * (n / j) >= 4;
                    assert j >= k && k * k > n;
                    assert j * j > n;
                    assert j > n / j;
                    assert n / j < j;
                    assert n / j < k;
                    assert n % (n / j) != 0;
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
        return false;
    }
    
    var prime1 := IsPrime(factors[0]);
    var prime2 := IsPrime(factors[1]);
    var prime3 := IsPrime(factors[2]);
    
    if prime1 && prime2 && prime3 {
        assert Prime(factors[0]) && Prime(factors[1]) && Prime(factors[2]);
        assert SeqProduct(factors) == x;
        SeqProductCorrect(factors);
        assert x == factors[0] * SeqProduct(factors[1..]);
        SeqProductCorrect(factors[1..]);
        assert SeqProduct(factors[1..]) == factors[1] * SeqProduct(factors[2..]);
        assert SeqProduct(factors[2..]) == factors[2];
        assert x == factors[0] * factors[1] * factors[2];
        return true;
    }
    
    return false;
}
// </vc-code>

