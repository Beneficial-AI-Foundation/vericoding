

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a == old(a)
ensures b.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> b[i] == a[a.Length - i - 1]
// </vc-spec>
// <vc-code>
{
    var n := a.Length;
    b := new char[n];

    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> b[k] == a[n - k - 1]
        invariant b.Length == n
        invariant a.Length == n
    {
        b[i] := a[n - i - 1];
        i := i + 1;
    }
    return b;
}
// </vc-code>

