predicate ValidInput(N: int) {
    100 <= N <= 999
}

predicate ContainsSeven(N: int) 
    requires ValidInput(N)
{
    (N % 10) == 7 || ((N / 10) % 10) == 7 || (N / 100) == 7
}

predicate ValidOutput(result: string) {
    result == "Yes\n" || result == "No\n"
}

// <vc-helpers>
function Digits(N: int) : seq<int>
    requires 100 <= N <= 999
    ensures forall d | d in Digits(N) :: 0 <= d <= 9
    ensures |Digits(N)| == 3
{
    var d0 := N % 10;
    var d1 := (N / 10) % 10;
    var d2 := N / 100;
    [d2, d1, d0]
}

lemma ContainsSeven_Digits(N: int)
    requires ValidInput(N)
    ensures ContainsSeven(N) <==> (exists d | d in Digits(N) :: d == 7)
{
    var digits := Digits(N);
    calc {
        ContainsSeven(N);
        (N % 10) == 7 || ((N / 10) % 10) == 7 || (N / 100) == 7;
        {
            assert digits[2] == N % 10;
            assert digits[1] == (N / 10) % 10;
            assert digits[0] == N / 100;
        }
        digits[2] == 7 || digits[1] == 7 || digits[0] == 7;
        (exists k :: 0 <= k < |digits| && digits[k] == 7);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: string)
    requires ValidInput(N)
    ensures ValidOutput(result)
    ensures result == "Yes\n" <==> ContainsSeven(N)
// </vc-spec>
// <vc-code>
{
    var digits := Digits(N);
    var foundSeven := false;
    // Iterate through the digits of N to check for a 7
    // N is a 3-digit number (100 <= N <= 999), so it has 3 digits.
    // The Digits function returns them as seq<int> of length 3.
    // The current version of Dafny Playground does not support for loops with sequence iteration.
    // So, we'll manually check each digit.

    if digits[0] == 7 {
        foundSeven := true;
    } else if digits[1] == 7 {
        foundSeven := true;
    } else if digits[2] == 7 {
        foundSeven := true;
    }

    if foundSeven {
        result := "Yes\n";
    } else {
        result := "No\n";
    }

    // Proof to link ContainsSeven and foundSeven
    ContainsSeven_Digits(N);
    assert (exists d | d in digits :: d == 7) <==> (digits[0] == 7 || digits[1] == 7 || digits[2] == 7);
    assert (digits[0] == 7 || digits[1] == 7 || digits[2] == 7) <==> foundSeven;
    assert (exists d | d in digits :: d == 7) <==> foundSeven;
    assert ContainsSeven(N) <==> foundSeven;

    // Proof to link result and ContainsSeven
    if ContainsSeven(N) {
        assert result == "Yes\n";
    } else {
        assert result == "No\n";
    }
}
// </vc-code>

