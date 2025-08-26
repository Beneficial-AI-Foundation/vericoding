// <vc-spec>
method mezclar(V: array<int>, c: int, m: int, f: int)
    requires 0 <= c <= m < f <= V.Length
    modifies V
{
    // Placeholder merge implementation
}

method ordenar_mergesort(V : array?<int>)

    requires V != null

    modifies V

{

    mergesort(V, 0, V.Length - 1) ;

}

// <vc-helpers>
// </vc-helpers>

method mergesort(V : array?<int>, c : int, f : int) 

    requires V != null
    requires c >= 0 && f <= V.Length

    decreases f - c

    modifies V
// </vc-spec>
// <vc-code>
{
    if c < f {
        var m := c + (f - c) / 2;
        mergesort(V, c, m);
        mergesort(V, m + 1, f);
        if m + 1 <= f {
            mezclar(V, c, m, f);
        }
    }
}
// </vc-code>