// IMPL
method Reverse(a: array<int>)
	modifies a;
	ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
{
    var i := 0;
    while i < a.Length / 2
        invariant 0 <= i <= a.Length / 2
        invariant forall k :: 0 <= k < i ==> a[k] == old(a[(a.Length-1) - k])
        invariant forall k :: 0 <= k < i ==> a[(a.Length-1) - k] == old(a[k])
        invariant forall k :: i <= k <= (a.Length-1) - i ==> a[k] == old(a[k])
    {
        var temp := a[i];
        a[i] := a[(a.Length-1) - i];
        a[(a.Length-1) - i] := temp;
        i := i + 1;
    }
}


// IMPL

method ReverseUptoK(s: array<int>, k: int)
    modifies s
    requires 2 <= k <= s.Length
    ensures forall i :: 0 <= i < k ==> s[i] == old(s[k - 1 - i])
    ensures forall i :: k <= i < s.Length ==> s[i] == old(s[i])
{
    var i := 0;
    while i < k / 2
        invariant 0 <= i <= k / 2
        invariant forall j :: 0 <= j < i ==> s[j] == old(s[k - 1 - j])
        invariant forall j :: 0 <= j < i ==> s[k - 1 - j] == old(s[j])
        invariant forall j :: i <= j <= k - 1 - i ==> s[j] == old(s[j])
        invariant forall j :: k <= j < s.Length ==> s[j] == old(s[j])
    {
        var temp := s[i];
        s[i] := s[k - 1 - i];
        s[k - 1 - i] := temp;
        i := i + 1;
    }
}