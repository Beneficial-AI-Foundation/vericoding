// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result == (forall i :: 0 <= i < a.Length ==> n > a[i])
// </vc-spec>
// <vc-code>
{
    var i := 0;
    result := true;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result <==> (forall k :: 0 <= k < i ==> n > a[k])
        decreases a.Length - i
    {
        result := result && (n > a[i]);
        i := i + 1;
    }
}
// </vc-code>
