predicate IsLowercaseLetter(c: char)
{
    'a' <= c <= 'z'
}

predicate AllLowercase(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> IsLowercaseLetter(s[i])
}

predicate ValidOutput(result: string)
{
    result == "A" || result == "a"
}

// <vc-helpers>
lemma AllLowercaseEmpty(s: string)
    ensures |s| == 0 ==> !AllLowercase(s)
{
    if |s| == 0 {
        assert !AllLowercase(s);
    }
}

lemma AllLowercaseNonEmpty(s: string)
    ensures |s| > 0 ==> (AllLowercase(s) == forall i :: 0 <= i < |s| ==> IsLowercaseLetter(s[i]))
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures ValidOutput(result)
    ensures AllLowercase(input) ==> result == "a"
    ensures (|input| == 0 || !AllLowercase(input)) ==> result == "A"
// </vc-spec>
// <vc-code>
{
    if |input| > 0 {
        var i := 0;
        while i < |input|
            invariant 0 <= i <= |input|
            invariant forall j :: 0 <= j < i ==> IsLowercaseLetter(input[j])
        {
            if !IsLowercaseLetter(input[i]) {
                result := "A";
                return;
            }
            i := i + 1;
        }
        result := "a";
    } else {
        result := "A";
    }
}
// </vc-code>

