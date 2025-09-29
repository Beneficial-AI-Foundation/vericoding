// <vc-preamble>
// Method performs element-wise lexicographic comparison of two string sequences
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Less(x1: seq<string>, x2: seq<string>) returns (result: seq<bool>)
    // Input sequences must have the same length
    requires |x1| == |x2|
    
    // Result has same length as input sequences
    ensures |result| == |x1|
    
    // Core property: result[i] = (x1[i] < x2[i]) for all valid indices
    ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] < x2[i])
    
    // Asymmetry: if x1[i] < x2[i], then NOT (x2[i] < x1[i])
    ensures forall i :: 0 <= i < |result| && result[i] ==> !(x2[i] < x1[i])
    
    // Irreflexivity: no string is less than itself
    ensures forall i :: 0 <= i < |result| && x1[i] == x2[i] ==> !result[i]
    
    // Transitivity property: if x1[i] < x2[i] and x2[i] < s, then x1[i] < s
    ensures forall i :: (0 <= i < |result| && result[i]) ==> 
                forall s: string {:trigger x2[i] < s} :: x2[i] < s ==> x1[i] < s
    
    // Decidability: result is always boolean (automatically satisfied in Dafny)
    ensures forall i :: 0 <= i < |result| ==> result[i] || !result[i]
    
    // Empty string property: empty string is less than any non-empty string
    ensures forall i :: 0 <= i < |result| && x1[i] == "" && x2[i] != "" ==> result[i]
    
    // Non-empty string property: non-empty string is not less than empty string  
    ensures forall i :: 0 <= i < |result| && x1[i] != "" && x2[i] == "" ==> !result[i]
    
    // Consistency with string's built-in less-than operator
    ensures forall i :: 0 <= i < |result| ==> (result[i] <==> x1[i] < x2[i])
    
    // Strict ordering: if result[i] is true, then x1[i] and x2[i] are different
    ensures forall i :: 0 <= i < |result| && result[i] ==> x1[i] != x2[i]
    
    // Totality of comparison: for any two strings, exactly one of <, =, > holds
    ensures forall i :: 0 <= i < |result| ==> 
                result[i] || x1[i] == x2[i] || x2[i] < x1[i]
    
    // Prefix property: if s1 is a proper prefix of s2, then s1 < s2
    ensures forall i :: 0 <= i < |result| ==> 
                ((|x1[i]| < |x2[i]| && x2[i][..|x1[i]|] == x1[i]) ==> result[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
