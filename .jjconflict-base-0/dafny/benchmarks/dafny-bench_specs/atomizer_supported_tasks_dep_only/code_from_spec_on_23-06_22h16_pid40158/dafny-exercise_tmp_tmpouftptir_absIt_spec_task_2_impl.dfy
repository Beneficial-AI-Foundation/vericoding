//IMPL AbsIt
method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
{
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant forall j :: 0 <= j < i ==> if old(s[j]) < 0 then s[j] == -old(s[j]) else s[j] == old(s[j])
        invariant forall j :: i <= j < s.Length ==> s[j] == old(s[j])
    {
        if s[i] < 0 {
            s[i] := -s[i];
        }
        i := i + 1;
    }
}

//IMPL Tester
method Tester()
{
}