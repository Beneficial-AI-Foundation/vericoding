predicate ValidInput(s: string)
{
    |s| >= 1 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

function ExpectedLength(s: string): nat
{
    (|s| + 1) / 2
}

predicate CorrectExtraction(s: string, result: string)
{
    |result| == ExpectedLength(s) &&
    forall i :: 0 <= i < |result| ==> 0 <= 2*i < |s| && result[i] == s[2*i] &&
    forall i :: 0 <= i < |s| && i % 2 == 0 ==> exists j :: 0 <= j < |result| && result[j] == s[i] && j == i / 2
}

// <vc-helpers>
lemma LemmaEvenIndexBound(s: string, i: int)
    requires 0 <= i < ExpectedLength(s)
    ensures 0 <= 2*i < |s|
{
    var n := ExpectedLength(s);
    assert i <= n-1;   // because i < n and i, n are integers

    // We know: 2 * n <= |s|+1
    assert 2 * n <= |s|+1;

    // Now, we show that 2*(n-1) <= |s| - 1.
    calc {
        2*(n-1);
        == 2*n - 2;
        <= (|s|+1) - 2;   // because 2*n <= |s|+1, so 2*n-2 <= (|s|+1)-2
        == |s| - 1;
    }

    // Now, since i <= n-1, we have 2*i <= 2*(n-1) (because 2 is nonnegative)
    assert 2*i <= 2*(n-1);
    // Then, by the above, 2*(n-1) <= |s| - 1, so 2*i <= |s| - 1 < |s|.
    assert 2*i < |s|;
}

lemma LemmaAllEvenIndicesInRange(s: string)
    requires ValidInput(s)
    ensures forall i :: 0 <= i < ExpectedLength(s) ==> 0 <= 2*i < |s|
{
    var n := ExpectedLength(s);
    forall i | 0 <= i < n
        ensures 0 <= 2*i < |s|
    {
        LemmaEvenIndexBound(s, i);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures CorrectExtraction(s, result)
// </vc-spec>
// <vc-code>
{
    var n := ExpectedLength(s);
    LemmaAllEvenIndicesInRange(s);
    var arr := new char[n];
    for i := 0 to n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> arr[j] == s[2*j]
        invariant i < n ==> 0 <= 2*i < |s|
    {
        arr[i] := s[2*i];
    }
    result := arr[..];
}
// </vc-code>

