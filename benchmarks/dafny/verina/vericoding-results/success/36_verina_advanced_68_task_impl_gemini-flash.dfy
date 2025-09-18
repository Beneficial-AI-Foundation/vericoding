// <vc-preamble>
predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}
// </vc-preamble>

// <vc-helpers>
lemma IsDigitCharProperty(c: char) returns (isDigit: bool)
{
  isDigit := '0' <= c && c <= '9';
}
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
    if |input| == 0 {
        assert |result| == 0;
    }
    if |input| > 0 {
        assert |result| > 0;
        var i := 0;
        while i < |result|
            invariant 0 <= i <= |result|
            invariant forall j :: 0 <= j < i ==> (j % 2 == 0 ==> !IsDigit(result[j])) && (j % 2 == 1 ==> IsDigit(result[j]))
        {
            if i % 2 == 0 {
                assert !IsDigit(result[i]); 
            }
            else {
                assert IsDigit(result[i]);
            }
            i := i + 1;
        }
    }
}
// </vc-code>
