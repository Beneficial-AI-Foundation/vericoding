//IMPL 
method RemoveElement(s: array<int>, k: int) returns (v: array<int>)
    requires 0 <= k < s.Length
    ensures v.Length == s.Length - 1
    ensures forall i :: 0 <= i < k ==> v[i] == s[i]
    ensures forall i :: k <= i < v.Length ==> v[i] == s[i + 1]
{
    v := new int[s.Length - 1];
    
    // Copy elements before index k
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant forall j :: 0 <= j < i ==> v[j] == s[j]
    {
        v[i] := s[i];
        i := i + 1;
    }
    
    // Copy elements after index k, shifting them left
    while i < v.Length
        invariant k <= i <= v.Length
        invariant forall j :: 0 <= j < k ==> v[j] == s[j]
        invariant forall j :: k <= j < i ==> v[j] == s[j + 1]
    {
        v[i] := s[i + 1];
        i := i + 1;
    }
}