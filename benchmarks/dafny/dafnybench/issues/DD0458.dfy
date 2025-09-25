// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method firste(a: array<char>) returns (c:int)
ensures -1 <= c < a.Length
ensures 0 <= c < a.Length ==> a[c] == 'e' && forall x :: 0 <= x < c ==> a[x] != 'e'
ensures c == -1 ==> forall x :: 0 <= x < a.Length ==> a[x] != 'e'
// </vc-spec>
// <vc-code>
{
    var i:int := 0;
    while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: 0 <= x < i ==> a[x] != 'e'
    {
        if a[i] == 'e' {
            return i;
        }
        i := i + 1;
    }
    return -1;
}
// </vc-code>
