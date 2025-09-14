// <vc-preamble>
predicate IsLowerCase(c: char)
{
    'a' <= c && c <= 'z'
}

function ShiftMinus32(c: char): char
    requires 'a' <= c <= 'z'
{
    (c as int - 32) as char
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ToUppercase(s: string) returns (result: string)
    ensures
        |result| == |s|
    ensures
        forall i :: 0 <= i < |s| ==> 
            var c := s[i];
            var r := result[i];
            if IsLowerCase(c) then
                r == ShiftMinus32(c)
            else
                r == c
// </vc-spec>
// <vc-code>
{
    var res: seq<char> := [];
    for i: nat := 0 to |s|
        invariant |res| == i
        invariant forall j :: 0 <= j < i ==> res[j] == if IsLowerCase(s[j]) then ShiftMinus32(s[j]) else s[j]
    {
        var c := s[i];
        if IsLowerCase(c) {
            res := res + [ShiftMinus32(c)];
        } else {
            res := res + [c];
        }
    }
    result := res;
}
// </vc-code>
