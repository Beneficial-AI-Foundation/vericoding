// <vc-preamble>
// Helper function to compute modulo that handles negative numbers correctly
function Mod(x: int, n: nat): nat
  requires n > 0
{
  var r := x % n;
  if r < 0 then r + n else r
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no additional helper functions required */

// </vc-helpers>

// <vc-spec>
method Roll<T>(a: seq<T>, shift: int) returns (result: seq<T>)
  ensures |result| == |a|
  ensures |a| == 0 ==> result == a
  ensures |a| > 0 ==> forall i :: 0 <= i < |a| ==> 
    result[i] == a[Mod(i - shift, |a|)]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed compilation error for sequence initialization */
{
  if |a| == 0 {
    return a;
  }
  var n := |a|;
  var b := seq<T>(n, i => a[Mod(i - shift, n)]);
  return b;
}
// </vc-code>
