

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method join(a:array<int>,b:array<int>) returns (c:array<int>)
ensures a[..] + b[..] == c[..]
ensures multiset(a[..] + b[..]) == multiset(c[..])
ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
ensures a.Length+b.Length == c.Length

// Forall

ensures forall i :: 0<=i<a.Length ==> c[i] == a[i]
ensures forall i_2,j_2::
    a.Length <= i_2 < c.Length &&
    0<=j_2< b.Length && i_2 - j_2 == a.Length  ==> c[i_2] == b[j_2]
// </vc-spec>
// <vc-code>
{
    var c_length := a.Length + b.Length;
    c := new int[c_length];

    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> c[k] == a[k]
        invariant forall k :: i <= k < c.Length ==> c[k] == 0
    {
        c[i] := a[i];
        i := i + 1;
    }

    var j := 0;
    while j < b.Length
        invariant 0 <= j <= b.Length
        invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
        invariant forall k :: 0 <= k < j ==> c[a.Length + k] == b[k]
        invariant forall k :: a.Length + j <= k < c.Length ==> c[k] == 0
    {
        c[a.Length + j] := b[j];
        j := j + 1;
    }
}
// </vc-code>

