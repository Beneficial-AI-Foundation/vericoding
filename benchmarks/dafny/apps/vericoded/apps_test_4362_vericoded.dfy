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

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures ValidOutput(result)
    ensures AllLowercase(input) ==> result == "a"
    ensures (|input| == 0 || !AllLowercase(input)) ==> result == "A"
// </vc-spec>
// <vc-code>
{
    if |input| == 0 {
        result := "A";
    } else {
        var allLower := true;
        var i := 0;
        while i < |input|
            invariant 0 <= i <= |input|
            invariant allLower == (forall j :: 0 <= j < i ==> IsLowercaseLetter(input[j]))
        {
            if !IsLowercaseLetter(input[i]) {
                allLower := false;
            }
            i := i + 1;
        }
        
        if allLower {
            result := "a";
        } else {
            result := "A";
        }
    }
}
// </vc-code>

