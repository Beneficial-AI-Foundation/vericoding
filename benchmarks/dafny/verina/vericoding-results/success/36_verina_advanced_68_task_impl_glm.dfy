// <vc-preamble>
predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
lemma RunLengthEncoderProperty(input: string, result: string)
    requires
        // Non-empty check: input is empty iff result is empty
        (|input| == 0) <==> (|result| == 0)
    requires
        // Format validation: result alternates between characters and digits
        |result| > 0 ==> (
            forall i :: 0 <= i < |result| ==> 
                (i % 2 == 0 ==> !IsDigit(result[i])) &&
                (i % 2 == 1 ==> IsDigit(result[i]))
        )
// </vc-spec>
// <vc-code>
{
}
// </vc-code>
