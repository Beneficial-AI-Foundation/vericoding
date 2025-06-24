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
        invariant a in s[..i]
        invariant forall x :: 0 <= x < i ==> a >= s[x]
    {
        if s[i] > a {
            a := s[i];
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): Added assertion to help Dafny verify that a in s[..] follows from a in s[..i] when i == s.Length */
    assert i == s.Length;
    assert s[..i] == s[..];
}