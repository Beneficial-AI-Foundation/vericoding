//ATOM

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


//IMPL 

method Checker() {
  /* code modified by LLM (iteration 1): Added implementation to empty method body */
  // This method can be used to test the max function
  var arr := new nat[3];
  arr[0] := 5;
  arr[1] := 2;
  arr[2] := 8;
  var maximum := max(arr);
  assert maximum >= 5;
  assert maximum >= 2;
  assert maximum >= 8;
}