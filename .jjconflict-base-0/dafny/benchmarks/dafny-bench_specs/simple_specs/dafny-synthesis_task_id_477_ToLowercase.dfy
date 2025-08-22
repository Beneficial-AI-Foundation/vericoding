//ATOM

predicate IsUpperLowerPair(C : char, c : char)
{
  (C as int) == (c as int) - 32
}


//ATOM

function Shift32(c : char) : char
{
  ((c as int + 32) % 128) as char
}


//ATOM
predicate IsUpperCase(c : char)
{
  65 <= c as int <= 90
}


// SPEC

method ToLowercase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
}
