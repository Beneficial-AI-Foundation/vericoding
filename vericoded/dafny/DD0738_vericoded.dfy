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

// </vc-helpers>

// <vc-spec>
method ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
{
    var result := [];
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> 
            if IsUpperCase(s[j]) then IsUpperLowerPair(s[j], result[j]) 
            else result[j] == s[j]
    {
        if IsUpperCase(s[i]) {
            result := result + [Shift32(s[i])];
        } else {
            result := result + [s[i]];
        }
        i := i + 1;
    }
    
    v := result;
}
// </vc-code>

