// ATOM 
predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}


// ATOM 

predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}


// ATOM 

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}


// ATOM 

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}


// ATOM 

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}


// ATOM 

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}


// SPEC 

method ToggleCase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
}
