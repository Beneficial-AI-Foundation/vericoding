predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsProductEven(a: array<int>) returns (result: bool)
    ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
// </vc-spec>
// <vc-code>
{
    if a.Length == 0 {
        return false;
    }
    
    var k := 0;
    while k < a.Length
        invariant 0 <= k <= a.Length
        invariant forall i :: 0 <= i < k ==> !IsEven(a[i])
    {
        if IsEven(a[k]) {
            return true;
        }
        k := k + 1;
    }
    
    return false;
}
// </vc-code>

