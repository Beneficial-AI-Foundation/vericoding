predicate triple(a: array<int>) 
reads a
{
    exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}

// <vc-helpers>
lemma TripleExists(a: array<int>, i: int)
requires 0 <= i < a.Length - 2
requires a[i] == a[i + 1] == a[i + 2]
ensures triple(a)
{
}

lemma NoTripleFound(a: array<int>, k: int)
requires 0 <= k <= a.Length - 2
requires forall j :: 0 <= j < k ==> !(a[j] == a[j + 1] == a[j + 2])
requires k == a.Length - 2
ensures !triple(a)
{
    if triple(a) {
        var i :| 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2];
        assert 0 <= i < k + 1;
        assert i < k || i == k;
        if i < k {
            assert !(a[i] == a[i + 1] == a[i + 2]);
            assert false;
        } else {
            assert i == k;
            assert i == a.Length - 2;
            assert !(a[i] == a[i + 1] == a[i + 2]);
            assert false;
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a.Length < 3 {
        index := a.Length;
        return;
    }
    
    index := 0;
    while index < a.Length - 2
    invariant 0 <= index <= a.Length - 2
    invariant forall j :: 0 <= j < index ==> !(a[j] == a[j + 1] == a[j + 2])
    {
        if a[index] == a[index + 1] == a[index + 2] {
            TripleExists(a, index);
            return;
        }
        index := index + 1;
    }
    
    if index == a.Length - 2 {
        NoTripleFound(a, index);
    }
    
    index := a.Length;
}
// </vc-code>
