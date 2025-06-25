//ATOM

method max(s: array<nat>) returns (a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
{
  a := 0;
  assume forall x :: 0 <= x < s.Length ==> a >= s[x];
  assume a in s[..];
  return a;
}


// SPEC

method Checker() {
}
