method AbsIt(s: array<int>) modifies s
ensures forall x :: 0 <= x < s.Length ==> old(s[x]) < 0 ==> s[x] == -old(s[x])
ensures forall x :: 0 <= x < s.Length ==> old(s[x]) >= 0 ==> s[x] == old(s[x])
{
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant forall x :: 0 <= x < i ==> old(s[x]) < 0 ==> s[x] == -old(s[x])
        invariant forall x :: 0 <= x < i ==> old(s[x]) >= 0 ==> s[x] == old(s[x])
        invariant forall x :: i <= x < s.Length ==> s[x] == old(s[x])
    {
        if s[i] < 0 {
            s[i] := -s[i];
        }
        i := i + 1;
    }
}