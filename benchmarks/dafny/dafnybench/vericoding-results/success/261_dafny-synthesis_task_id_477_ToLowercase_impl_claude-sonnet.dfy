predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

// <vc-helpers>
lemma ShiftCorrectness(c: char)
    requires IsUpperCase(c)
    ensures IsUpperLowerPair(c, Shift32(c))
{
    assert 65 <= c as int <= 90;
    assert c as int + 32 <= 122;
    assert c as int + 32 < 128;
    assert (c as int + 32) % 128 == c as int + 32;
    assert Shift32(c) as int == c as int + 32;
    assert IsUpperLowerPair(c, Shift32(c));
}
// </vc-helpers>

// <vc-spec>
method ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
{
    v := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |v| == i
        invariant forall j :: 0 <= j < i ==> if IsUpperCase(s[j]) then IsUpperLowerPair(s[j], v[j]) else v[j] == s[j]
    {
        if IsUpperCase(s[i]) {
            ShiftCorrectness(s[i]);
            v := v + [Shift32(s[i])];
        } else {
            v := v + [s[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

