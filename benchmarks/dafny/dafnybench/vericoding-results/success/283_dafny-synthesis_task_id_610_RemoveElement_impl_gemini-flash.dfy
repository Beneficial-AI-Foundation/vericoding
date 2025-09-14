

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveElement(s: array<int>, k: int) returns (v: array<int>)
    requires 0 <= k < s.Length
    ensures v.Length == s.Length - 1
    ensures forall i :: 0 <= i < k ==> v[i] == s[i]
    ensures forall i :: k <= i < v.Length ==> v[i] == s[i + 1]
// </vc-spec>
// <vc-code>
{
    var n := s.Length;
    v := new int[n - 1];

    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant forall j :: 0 <= j < i ==> v[j] == s[j]
    {
        v[i] := s[i];
        i := i + 1;
    }

    var j := k;
    while j < n - 1
        invariant k <= j < n
        invariant forall l :: k <= l < j ==> v[l] == s[l + 1]
        invariant forall l :: 0 <= l < k ==> v[l] == s[l]
    {
        v[j] := s[j + 1];
        j := j + 1;
    }

    return v;
}
// </vc-code>

