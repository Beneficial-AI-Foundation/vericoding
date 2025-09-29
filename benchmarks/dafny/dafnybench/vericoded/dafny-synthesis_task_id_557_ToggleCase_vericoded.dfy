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
lemma ShiftMinus32Correct(c: char)
    requires IsLowerCase(c)
    ensures IsLowerUpperPair(c, ShiftMinus32(c))
{
    var result := ShiftMinus32(c);
    assert (c as int) - 32 >= 65;
    assert (c as int) - 32 <= 90;
    assert ((c as int - 32) % 128) == (c as int) - 32;
    assert (result as int) == (c as int) - 32;
    assert IsLowerUpperPair(c, result);
}

lemma Shift32Correct(c: char)
    requires IsUpperCase(c)
    ensures IsUpperLowerPair(c, Shift32(c))
{
    var result := Shift32(c);
    assert (c as int) + 32 >= 97;
    assert (c as int) + 32 <= 122;
    assert ((c as int + 32) % 128) == (c as int) + 32;
    assert (result as int) == (c as int) + 32;
    assert IsUpperLowerPair(c, result);
}
// </vc-helpers>

// <vc-spec>
method ToggleCase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
{
    var result := [];
    for i := 0 to |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> 
            if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], result[j]) 
            else if IsUpperCase(s[j]) then IsUpperLowerPair(s[j], result[j]) 
            else result[j] == s[j]
    {
        if IsLowerCase(s[i]) {
            ShiftMinus32Correct(s[i]);
            result := result + [ShiftMinus32(s[i])];
        } else if IsUpperCase(s[i]) {
            Shift32Correct(s[i]);
            result := result + [Shift32(s[i])];
        } else {
            result := result + [s[i]];
        }
    }
    return result;
}
// </vc-code>

