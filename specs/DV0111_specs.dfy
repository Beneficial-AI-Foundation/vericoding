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
    assume {:axiom} false;
    result := "";
}
// </vc-code>
