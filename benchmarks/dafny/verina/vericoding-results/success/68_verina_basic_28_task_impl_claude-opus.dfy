// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPrime(n: nat) returns (result: bool)
    requires n >= 2
    ensures result ==> forall k: nat :: 2 <= k < n ==> n % k != 0
    ensures !result ==> exists k: nat :: 2 <= k < n && n % k == 0
// </vc-spec>
// <vc-code>
{
    var i := 2;
    result := true;
    
    while i < n
        invariant 2 <= i <= n
        invariant result ==> forall k: nat :: 2 <= k < i ==> n % k != 0
        invariant !result ==> exists k: nat :: 2 <= k < i && n % k == 0
    {
        if n % i == 0 {
            result := false;
            return;
        }
        i := i + 1;
    }
}
// </vc-code>
