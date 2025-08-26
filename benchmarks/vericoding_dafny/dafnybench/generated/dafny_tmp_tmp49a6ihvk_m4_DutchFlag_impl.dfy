datatype Color = Red | White | Blue

predicate Below(c: Color, d: Color)
{
    c == Red || c == d || d == Blue
}

// <vc-helpers>
lemma BelowTransitive(a: Color, b: Color, c: Color)
    requires Below(a, b) && Below(b, c)
    ensures Below(a, c)
{
    // Dafny can prove this automatically
}

lemma BelowProperties(c: Color, d: Color)
    ensures Below(Red, d)
    ensures Below(c, Blue)
    ensures Below(c, c)
{
    // Dafny can prove this automatically
}
// </vc-helpers>

// <vc-spec>
method DutchFlag(a: array<Color>)
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
    ensures multiset(a[..]) == multiset(old(a[..]))
// </vc-spec>
// <vc-code>
{
    if a.Length <= 1 {
        return;
    }
    
    var low := 0;
    var mid := 0;
    var high := a.Length - 1;
    
    while mid <= high
        invariant 0 <= low <= mid <= high + 1 <= a.Length
        invariant forall k :: 0 <= k < low ==> a[k] == Red
        invariant forall k :: low <= k < mid ==> a[k] == White
        invariant forall k :: high < k < a.Length ==> a[k] == Blue
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        if a[mid] == Red {
            a[low], a[mid] := a[mid], a[low];
            low := low + 1;
            mid := mid + 1;
        } else if a[mid] == White {
            mid := mid + 1;
        } else { // a[mid] == Blue
            a[mid], a[high] := a[high], a[mid];
            high := high - 1;
        }
    }
}
// </vc-code>