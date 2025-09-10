predicate ValidInput(input: string)
{
    |input| >= 3 &&
    forall i :: 0 <= i < 3 ==> (input[i] == '1' || input[i] == '9')
}

function SwapDigit(c: char): char
    requires c == '1' || c == '9'
{
    if c == '1' then '9' else '1'
}

function TransformString(s: string): string
    requires |s| >= 3
    requires forall i :: 0 <= i < 3 ==> (s[i] == '1' || s[i] == '9')
{
    [SwapDigit(s[0]), SwapDigit(s[1]), SwapDigit(s[2])]
}

predicate ValidOutput(input: string, result: string)
    requires ValidInput(input)
{
    |result| == 4 &&
    result[3] == '\n' &&
    forall i :: 0 <= i < 3 ==> 
        (input[i] == '1' ==> result[i] == '9') && 
        (input[i] == '9' ==> result[i] == '1')
}

// <vc-helpers>
lemma lemma_TransformString(s: string)
    requires |s| >= 3
    requires forall i :: 0 <= i < 3 ==> (s[i] == '1' || s[i] == '9')
    ensures forall i :: 0 <= i < 3 ==> (
        (s[i] == '1' ==> TransformString(s)[i] == '9') &&
        (s[i] == '9' ==> TransformString(s)[i] == '1')
    )
    ensures |TransformString(s)| == 3
{
    // This lemma is implicitly proven due to the definition of TransformString
    // and SwapDigit, but we can make the property explicit if needed.
    // For example, for i=0:
    assert (s[0] == '1' ==> TransformString(s)[0] == SwapDigit(s[0]) == '9');
    assert (s[0] == '9' ==> TransformString(s)[0] == SwapDigit(s[0]) == '1');
    // and similarly for i=1 and i=2.
    // The length is also explicit from the construction [s_0, s_1, s_2].
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var transformed := TransformString(input);
    lemma_TransformString(input);
    result := transformed + "\n";

    // Prove |result| == 4
    assert |transformed| == 3;
    assert |"\n"| == 1;
    assert |result| == |transformed| + |"\n"|;
    assert |result| == 3 + 1 == 4;

    // Prove result[3] == '\n'
    assert result[3] == '\n';

    // Prove forall i :: 0 <= i < 3 ==> ( (input[i] == '1' ==> result[i] == '9') && (input[i] == '9' ==> result[i] == '1') )
    forall i | 0 <= i < 3
        ensures (input[i] == '1' ==> result[i] == '9')
        ensures (input[i] == '9' ==> result[i] == '1')
    {
        assert transformed[i] == result[i];
        assert (input[i] == '1' ==> transformed[i] == '9'); // From lemma_TransformString
        assert (input[i] == '9' ==> transformed[i] == '1'); // From lemma_TransformString
    }
}
// </vc-code>

