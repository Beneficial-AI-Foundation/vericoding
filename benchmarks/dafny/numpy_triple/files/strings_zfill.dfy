// <vc-preamble>
// Helper function to create a string of repeated characters
ghost function RepeatChar(c: char, n: nat): string
{
    if n == 0 then "" else [c] + RepeatChar(c, n - 1)
}

// Helper function to check if a character is a sign
ghost predicate IsSign(c: char)
{
    c == '+' || c == '-'
}

// Helper function to get the maximum of two natural numbers
ghost function Max(a: nat, b: nat): nat
{
    if a >= b then a else b
}

// Main zfill method specification
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ZFill(a: seq<string>, width: nat) returns (result: seq<string>)
    requires width >= 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==>
        var original := a[i];
        var output := result[i];
        // 1. Length invariant: result length is exactly max(original_length, width)
        |output| == Max(|original|, width) &&
        
        // 2. Identity morphism: strings already >= width are unchanged
        (|original| >= width ==> output == original) &&
        
        // 3. Zero-padding for short strings without signs
        (|original| < width && |original| > 0 && 
         !IsSign(original[0]) ==>
         exists padding :: padding == RepeatChar('0', width - |original|) &&
                          output == padding + original) &&
        
        // 4. Sign preservation: leading '+' or '-' are preserved at start
        (|original| < width && |original| > 0 && IsSign(original[0]) ==>
         exists sign, rest, padding ::
         sign == original[0] &&
         rest == original[1..] &&
         padding == RepeatChar('0', width - |original|) &&
         output == [sign] + padding + rest) &&
        
        // 5. Empty string handling: empty strings become all zeros
        (|original| == 0 ==> 
         |output| == width &&
         output == RepeatChar('0', width)) &&
        
        // 6. Minimality constraint: no over-padding
        (|original| >= width ==> |output| == |original|) &&
        
        // 7. Exactness constraint: padding achieves exact width requirement
        (|original| < width ==> |output| == width) &&
        
        // 8. Correctness constraint: result contains original content properly
        (|original| < width && |original| > 0 && !IsSign(original[0]) ==>
         output[width - |original|..] == original) &&
        
        // 9. Zero character constraint: padding uses only '0' characters
        (|original| < width && !IsSign(original[0]) ==>
         forall j :: 0 <= j < width - |original| ==> output[j] == '0') &&
         
        // Additional constraint for signed strings: padding after sign is all zeros
        (|original| < width && |original| > 0 && IsSign(original[0]) ==>
         forall j :: 1 <= j < width - |original| + 1 ==> output[j] == '0')
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
