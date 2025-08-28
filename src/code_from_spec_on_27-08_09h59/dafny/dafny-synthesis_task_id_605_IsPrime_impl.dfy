// <vc-helpers>
lemma DivisionProperty(n: int, k: int)
    requires n >= 2 && k >= 2
    ensures n % k == 0 <==> exists q :: q >= 1 && n == k * q

lemma PrimeCharacterization(n: int)
    requires n >= 2
    ensures (forall k :: 2 <= k < n ==> n % k != 0) <==> (forall k :: 2 <= k <= n - 1 ==> n % k != 0)
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IsPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (forall k :: 2 <= k < n ==> n % k != 0)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var i := 2;
    while i < n
        invariant 2 <= i <= n
        invariant forall k :: 2 <= k < i ==> n % k != 0
    {
        if n % i == 0 {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>
