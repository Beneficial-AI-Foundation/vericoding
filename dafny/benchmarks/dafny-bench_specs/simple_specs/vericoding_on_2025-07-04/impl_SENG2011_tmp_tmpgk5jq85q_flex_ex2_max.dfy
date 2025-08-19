//IMPL 
method max(s: array<nat>) returns (a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
{
    a := s[0];
    var i := 1;
    while i < s.Length
        invariant 1 <= i <= s.Length
        invariant forall x :: 0 <= x < i ==> a >= s[x]
        invariant a in s[0..i]
    {
        if s[i] > a {
            a := s[i];
        }
        i := i + 1;
    }
}