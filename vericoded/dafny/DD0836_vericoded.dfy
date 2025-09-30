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
    // Proof by cases on the colors
}

lemma PartitionInvariant(a: array<Color>, low: int, mid: int, high: int)
    requires 0 <= low <= mid <= high + 1 <= a.Length
    requires forall i :: 0 <= i < low ==> a[i] == Red
    requires forall i :: low <= i < mid ==> a[i] == White
    requires forall i :: high < i < a.Length ==> a[i] == Blue
    ensures forall i, j :: 0 <= i < low && low <= j < mid ==> Below(a[i], a[j])
    ensures forall i, j :: 0 <= i < low && high < j < a.Length ==> Below(a[i], a[j])
    ensures forall i, j :: low <= i < mid && high < j < a.Length ==> Below(a[i], a[j])
{
    // This follows from the partition properties and the definition of Below
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
    var low := 0;
    var mid := 0;
    var high := a.Length - 1;
    
    while mid <= high
        invariant 0 <= low <= mid <= high + 1 <= a.Length
        invariant forall i :: 0 <= i < low ==> a[i] == Red
        invariant forall i :: low <= i < mid ==> a[i] == White
        invariant forall i :: high < i < a.Length ==> a[i] == Blue
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        if a[mid] == Red {
            // Swap a[low] and a[mid]
            var temp := a[low];
            a[low] := a[mid];
            a[mid] := temp;
            low := low + 1;
            mid := mid + 1;
        } else if a[mid] == White {
            mid := mid + 1;
        } else { // a[mid] == Blue
            // Swap a[mid] and a[high]
            var temp := a[mid];
            a[mid] := a[high];
            a[high] := temp;
            high := high - 1;
        }
    }
}
// </vc-code>

