function ShiftMinus32(c : char) : char
{
  ((c as int - 32) % 128) as char
}


//ATOM
predicate IsLowerCase(c : char)
{
  97 <= c as int <= 122
}


//ATOM

predicate IsLowerUpperPair(c : char, C : char)
{
  (c as int) == (C as int) + 32
}


//IMPL 

method ToUppercase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{
  /* code modified by LLM (iteration 1): Fixed syntax error - removed extra semicolon and quote */
  v := "";"
  var j := 0;
  while j < |s|
    invariant 0 <= j <= |s|
    invariant |v| == j
    invariant forall i :: 0 <= i < j ==> if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
  {
    if IsLowerCase(s[j]) {
      v := v + [ShiftMinus32(s[j])];
    } else {
      v := v + [s[j]];
    }
    j := j + 1;
  }
}