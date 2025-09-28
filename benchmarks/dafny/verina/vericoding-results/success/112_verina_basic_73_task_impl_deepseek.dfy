// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function MatchChar(a: char, b: char): bool
{
    a == b || b == '?'
}

// </vc-helpers>

// <vc-spec>
method MatchStrings(s: string, p: string) returns (result: bool)
    requires |s| == |p|
    ensures result == (forall n :: 0 <= n < |s| ==> 
        (s[n] == p[n] || p[n] == '?'))
// </vc-spec>
// <vc-code>
{
    var i := 0;
    result := true;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result == (forall j :: 0 <= j < i ==> MatchChar(s[j], p[j]))
    {
        if !MatchChar(s[i], p[i]) {
            result := false;
            return;
        }
        i := i + 1;
    }
}
// </vc-code>
