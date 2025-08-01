// IMPL 
method leq(a: array<int>, b: array<int>) returns (result: bool) 
    ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{
    var i := 0;
    while i < a.Length && i < b.Length
        invariant 0 <= i <= a.Length && i <= b.Length
        invariant a[..i] == b[..i]
    {
        if a[i] < b[i] {
            result := true;
            return;
        } else if a[i] > b[i] {
            result := false;
            return;
        }
        i := i + 1;
    }
    
    // If we get here, a[..i] == b[..i] where i == min(a.Length, b.Length)
    result := a.Length <= b.Length;
}

// IMPL 
method testLeq() {
}