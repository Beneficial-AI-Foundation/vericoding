predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsInteger(s: string) returns (result: bool)
    ensures result <==> (|s| > 0) && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
// </vc-spec>
// <vc-code>
{
    if |s| == 0 {
        return false;
    }
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> IsDigit(s[j])
    {
        if !IsDigit(s[i]) {
            return false;
        }
        i := i + 1;
    }
    
    return true;
}
// </vc-code>

