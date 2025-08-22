//IMPL AbsIt
method AbsIt(s: array<int>) 
modifies s
ensures forall x :: 0 <= x < s.Length ==> old(s[x]) < 0 ==> s[x] == -old(s[x])
ensures forall x :: 0 <= x < s.Length ==> old(s[x]) >= 0 ==> s[x] == old(s[x])
{
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant forall j :: 0 <= j < i ==> old(s[j]) < 0 ==> s[j] == -old(s[j])
        invariant forall j :: 0 <= j < i ==> old(s[j]) >= 0 ==> s[j] == old(s[j])
        invariant forall j :: i <= j < s.Length ==> s[j] == old(s[j])
    {
        if s[i] < 0 {
            s[i] := -s[i];
        }
        i := i + 1;
    }
}