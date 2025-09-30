predicate triple(a: array<int>) 
reads a
{
    exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
// </vc-spec>
// <vc-code>
{
    index := 0;
    while index < a.Length - 2
        invariant 0 <= index <= a.Length
        invariant forall i {:trigger a[i]} :: 0 <= i < index && i + 2 < a.Length ==> !(a[i] == a[i + 1] == a[i + 2])
    {
        if a[index] == a[index + 1] == a[index + 2] {
            return index;
        }
        index := index + 1;
    }
    index := a.Length;
}
// </vc-code>

