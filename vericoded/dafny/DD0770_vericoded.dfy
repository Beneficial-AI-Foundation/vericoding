predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
{
    var result := [];
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> 
            if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], result[j]) 
            else result[j] == s[j]
    {
        if IsLowerCase(s[i]) {
            var upperChar := ((s[i] as int - 32) as char);
            result := result + [upperChar];
        } else {
            result := result + [s[i]];
        }
        i := i + 1;
    }
    
    v := result;
}
// </vc-code>

