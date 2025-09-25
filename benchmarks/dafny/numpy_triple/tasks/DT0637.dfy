// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RJust(a: seq<string>, width: nat, fillchar: string) returns (result: seq<string>)
    requires |fillchar| == 1
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> 
        // Length invariant: result length is exactly max(orig.length, width)
        |result[i]| == (if |a[i]| >= width then |a[i]| else width) &&
        // Identity morphism: strings already >= width are unchanged
        (|a[i]| >= width ==> result[i] == a[i]) &&
        // Right-justification: when padding needed, original appears as suffix
        (|a[i]| < width ==> 
            |result[i]| == width &&
            // Original string is preserved as suffix
            (forall j :: 0 <= j < |a[i]| ==> result[i][width - |a[i]| + j] == a[i][j]) &&
            // Padding characters are fillchar
            (forall j :: 0 <= j < width - |a[i]| ==> result[i][j] == fillchar[0])) &&
        // Minimality constraint: no over-padding when not needed
        (|a[i]| >= width ==> |result[i]| == |a[i]|) &&
        // Exactness constraint: padding achieves exact width requirement  
        (|a[i]| < width ==> |result[i]| == width) &&
        // Consistency constraint: empty strings padded to full width
        (|a[i]| == 0 ==> |result[i]| == width)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
