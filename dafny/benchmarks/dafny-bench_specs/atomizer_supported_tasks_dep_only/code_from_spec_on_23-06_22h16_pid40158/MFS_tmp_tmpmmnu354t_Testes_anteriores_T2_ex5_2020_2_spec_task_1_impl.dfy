//IMPL 
method leq(a: array<int>, b: array<int>) returns (result: bool) 
    ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{
    var i := 0;
    var minLen := if a.Length <= b.Length then a.Length else b.Length;
    
    while i < minLen && a[i] == b[i]
        invariant 0 <= i <= minLen
        invariant minLen == (if a.Length <= b.Length then a.Length else b.Length)
        invariant forall j :: 0 <= j < i ==> a[j] == b[j]
        invariant i <= minLen ==> a[..i] == b[..i]
    {
        i := i + 1;
    }
    
    if i < minLen {
        // Found a differing position
        result := a[i] < b[i];
    } else {
        // All compared elements are equal
        result := a.Length <= b.Length;
    }
}

//ATOM_PLACEHOLDER_testLeq