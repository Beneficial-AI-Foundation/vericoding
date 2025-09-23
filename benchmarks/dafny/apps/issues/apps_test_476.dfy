// <vc-preamble>
predicate CanBeDecomposed(s: string)
{
    if |s| == 0 then true
    else if |s| >= 3 && s[|s|-3..] == "144" then CanBeDecomposed(s[..|s|-3])
    else if |s| >= 2 && s[|s|-2..] == "14" then CanBeDecomposed(s[..|s|-2])
    else if |s| >= 1 && s[|s|-1..] == "1" then CanBeDecomposed(s[..|s|-1])
    else false
}

predicate ValidInput(input: string)
{
    |input| > 0 &&
    (forall i :: 0 <= i < |input| ==> input[i] in "0123456789") &&
    (input[0] != '0' || |input| == 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanBeDecomposed(input)
// </vc-spec>
// <vc-code>
{
    var n := input;
    var good := true;

    while |n| > 0 && good
        decreases |n|
        invariant CanBeDecomposed(input) <==> CanBeDecomposed(n)
        invariant good ==> (|n| == 0 || (|n| >= 1 && n[|n|-1..] == "1") || (|n| >= 2 && n[|n|-2..] == "14") || (|n| >= 3 && n[|n|-3..] == "144") || !CanBeDecomposed(n))
    {
        if |n| >= 3 && n[|n|-3..] == "144" {
            n := n[..|n|-3];
        }
        else if |n| >= 2 && n[|n|-2..] == "14" {
            n := n[..|n|-2];
        }
        else if |n| >= 1 && n[|n|-1..] == "1" {
            n := n[..|n|-1];
        }
        else {
            good := false;
        }
    }

    if good {
        assert |n| == 0;
        assert CanBeDecomposed(n);
        assert CanBeDecomposed(input);
        result := "YES";
    } else {
        assert !CanBeDecomposed(n);
        assert !CanBeDecomposed(input);
        result := "NO";
    }
}
// </vc-code>
