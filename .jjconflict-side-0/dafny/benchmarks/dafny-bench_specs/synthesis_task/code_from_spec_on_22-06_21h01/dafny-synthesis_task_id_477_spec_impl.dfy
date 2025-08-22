// ATOM
predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}


// ATOM

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}


// ATOM

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}


// IMPL

method ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
    v := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |v| == i
        invariant forall j :: 0 <= j < i ==> if IsUpperCase(s[j]) then IsUpperLowerPair(s[j], v[j]) else v[j] == s[j]
    {
        if IsUpperCase(s[i]) {
            v := v + [Shift32(s[i])];
        } else {
            v := v + [s[i]];
        }
        i := i + 1;
    }
}