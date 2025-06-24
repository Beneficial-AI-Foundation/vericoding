//IMPL max
method max(s: array<nat>) returns (a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
{
    a := s[0];
    var i := 1;
    
    while i < s.Length
        invariant 1 <= i <= s.Length
        invariant a in s[..]
        invariant forall x :: 0 <= x < i ==> a >= s[x]
    {
        /* code modified by LLM (iteration 1): added assertion to help verification understand a remains in array after update */
        if s[i] > a {
            a := s[i];
            assert a == s[i];
            assert a in s[..];
        }
        i := i + 1;
    }
}

//IMPL Checker
method Checker() {
}