// flips (i.e., reverses) array elements in the range [0..num]

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method flip (a: array<int>, num: int)
requires a.Length > 0;
requires 0 <= num < a.Length;
modifies a;
ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num-k])
ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
// ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var j := num;
    var a_copy := old(a);

    while i < j
        invariant 0 <= i <= j <= num
        invariant forall k :: 0 <= k < i ==> a[k] == a_copy[num-k]
        invariant forall k :: j < k <= num ==> a[k] == a_copy[num-k]
        invariant forall k :: i <= k <= j ==> a[k] == a_copy[k] || a[k] == a_copy[num-k]
        invariant forall k :: num < k < a.Length ==> a[k] == a_copy[k]
        invariant multiset(a[..]) == multiset(a_copy[..])
    {
        a[i], a[j] := a[j], a[i];
        i := i + 1;
        j := j - 1;
    }
}
// </vc-code>

