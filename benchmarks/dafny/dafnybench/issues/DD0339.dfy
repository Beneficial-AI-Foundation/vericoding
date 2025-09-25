// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method leq(a: array<int>, b: array<int>) returns (result: bool) 
    ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < a.Length && i < b.Length 
        decreases a.Length - i
        invariant 0 <= i <= a.Length && 0 <= i <= b.Length
        invariant a[..i] == b[..i]
    {
        if a[i] < b[i] { return true; }
        else if a[i] > b[i] { return false; }
        else {i := i + 1; }
    }
    return a.Length <= b.Length;
}
// </vc-code>
