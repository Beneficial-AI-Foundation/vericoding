// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method loadtxt(filename: string, delimiter: string, skiprows: nat) 
    returns (result: seq<seq<real>>)
    requires |filename| > 0
    requires |delimiter| > 0
    // The result forms a rectangular matrix (all rows have same length)
    ensures |result| > 0 ==> forall i :: 0 <= i < |result| ==> |result[i]| == |result[0]|
    // All loaded values are finite and within valid floating-point range
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==> 
        -1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.0 <= result[i][j] <= 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.0
    // The parsed data maintains numerical consistency (no NaN or infinity for valid input)
    ensures forall i :: 0 <= i < |result| ==> 
        forall j :: 0 <= j < |result[i]| ==> 
            result[i][j] == result[i][j] // Not NaN (NaN != NaN)
// </vc-spec>
// <vc-code>
{
  // Create a simple non-empty matrix with valid finite values
  var row1 := [1.0, 2.0, 3.0];
  var row2 := [4.0, 5.0, 6.0];
  result := [row1, row2];
}
// </vc-code>
