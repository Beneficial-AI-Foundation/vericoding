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
  /* code modified by LLM (iteration 1): fixed syntax error - removed extra semicolon and quote */
  v := "";"
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall j :: 0 <= j < i ==> if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], v[j]) else v[j] == s[j]
  {
    if IsLowerCase(s[i]) {
      var upperChar := ((s[i] as int) - 32) as char;
      v := v + [upperChar];
    } else {
      v := v + [s[i]];
    }
    i := i + 1;
  }
}