

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
    v := new int[s.Length - 1];
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant forall j :: 0 <= j < i ==> v[j] == s[j]
    {
        v[i] := s[i];
        i := i + 1;
    }
    while i < v.Length
        invariant k <= i <= v.Length
        invariant forall j :: 0 <= j < k ==> v[j] == s[j]
        invariant forall j :: k <= j < i ==> v[j] == s[j + 1]
    {
        v[i] := s[i + 1];
        i := i + 1;
    }
}
// </vc-code>

