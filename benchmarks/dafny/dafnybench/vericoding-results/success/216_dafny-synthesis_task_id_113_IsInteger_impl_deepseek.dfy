predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

// <vc-helpers>
lemma AllDigits(s: string, i: int)
    requires 0 <= i <= |s|
    requires forall j :: 0 <= j < i ==> IsDigit(s[j])
    requires forall j :: i <= j < |s| ==> IsDigit(s[j])
    ensures forall j :: 0 <= j < |s| ==> IsDigit(s[j])
{
}
// </vc-helpers>

// <vc-spec>
method IsInteger(s: string) returns (result: bool)
    ensures result <==> (|s| > 0) && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
// </vc-spec>
// <vc-code>
{
    if |s| == 0 {
        result := false;
        return;
    }

    var i := 0;
    result := true;

    while i < |s|
        invariant 0 <= i <= |s|
        invariant result == (forall j :: 0 <= j < i ==> IsDigit(s[j]))
    {
        if !IsDigit(s[i]) {
            result := false;
            return;
        }
        i := i + 1;
        result := true; // Maintain result invariant
    }

    if result {
        // Prove final postcondition when all digits
        AllDigits(s, i);
    }
}
// </vc-code>

