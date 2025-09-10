predicate ValidInput(a: seq<int>)
{
    |a| >= 1
}

predicate CanBeDivided(a: seq<int>)
    requires ValidInput(a)
{
    |a| % 2 == 1 && a[0] % 2 == 1 && a[|a|-1] % 2 == 1
}

// <vc-helpers>
lemma LastIndexLemma(a: seq<int>)
    requires ValidInput(a)
    ensures |a| - 1 >= 0
{
}

lemma OddLengthOddEndsImpliesCanBeDivided(a: seq<int>)
    requires ValidInput(a)
    ensures (|a| % 2 == 1 && a[0] % 2 == 1 && a[|a|-1] % 2 == 1) == CanBeDivided(a)
{
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: string)
    requires ValidInput(a)
    ensures CanBeDivided(a) ==> result == "Yes"
    ensures !CanBeDivided(a) ==> result == "No"
// </vc-spec>
// <vc-code>
{
    LastIndexLemma(a);
    if |a| % 2 == 1 && a[0] % 2 == 1 && a[|a|-1] % 2 == 1 {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

