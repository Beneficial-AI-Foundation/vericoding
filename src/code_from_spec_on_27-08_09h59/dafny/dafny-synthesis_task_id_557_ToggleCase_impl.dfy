predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

// <vc-helpers>
lemma ShiftMinus32Properties(c: char)
    requires IsLowerCase(c)
    ensures IsUpperCase(ShiftMinus32(c))
    ensures IsLowerUpperPair(c, ShiftMinus32(c))
{
    assert 97 <= c as int <= 122;
    assert 65 <= c as int - 32 <= 90;
    assert IsUpperCase(ShiftMinus32(c));
    assert (c as int) == (ShiftMinus32(c) as int) + 32;
}

lemma Shift32Properties(c: char)
    requires IsUpperCase(c)
    ensures IsLowerCase(Shift32(c))
    ensures IsUpperLowerPair(c, Shift32(c))
{
    assert 65 <= c as int <= 90;
    assert 97 <= c as int + 32 <= 122;
    assert IsLowerCase(Shift32(c));
    assert (c as int) == (Shift32(c) as int) - 32;
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ToggleCase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    v := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |v| == i
        invariant forall j :: 0 <= j < i ==> 
            if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], v[j]) 
            else if IsUpperCase(s[j]) then IsUpperLowerPair(s[j], v[j]) 
            else v[j] == s[j]
    {
        if IsLowerCase(s[i]) {
            ShiftMinus32Properties(s[i]);
            v := v + [ShiftMinus32(s[i])];
        } else if IsUpperCase(s[i]) {
            Shift32Properties(s[i]);
            v := v + [Shift32(s[i])];
        } else {
            v := v + [s[i]];
        }
        i := i + 1;
    }
}
// </vc-code>
