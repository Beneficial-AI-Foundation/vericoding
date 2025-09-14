

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ReverseUptoK(s: array<int>, k: int)
    modifies s
    requires 2 <= k <= s.Length
    ensures forall i :: 0 <= i < k ==> s[i] == old(s[k - 1 - i])
    ensures forall i :: k <= i < s.Length ==> s[i] == old(s[i])
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var j := k - 1;
    
    while i < j
        invariant 0 <= i <= j + 1 <= k
        invariant j == k - 1 - i
        invariant forall m :: 0 <= m < i ==> s[m] == old(s[k - 1 - m])
        invariant forall m :: j < m < k ==> s[m] == old(s[k - 1 - m])
        invariant forall m :: i <= m <= j ==> s[m] == old(s[m])
        invariant forall m :: k <= m < s.Length ==> s[m] == old(s[m])
    {
        var temp := s[i];
        s[i] := s[j];
        s[j] := temp;
        
        i := i + 1;
        j := j - 1;
    }
}
// </vc-code>

