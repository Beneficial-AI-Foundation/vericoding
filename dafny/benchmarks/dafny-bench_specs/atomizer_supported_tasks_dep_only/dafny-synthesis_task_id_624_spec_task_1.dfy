// ATOM 
predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}


// ATOM 

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}


// ATOM 

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}


// SPEC 

method ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{
}


