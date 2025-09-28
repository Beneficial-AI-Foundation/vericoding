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

// </vc-helpers>

// <vc-spec>
method Roll<T>(a: seq<T>, shift: int) returns (result: seq<T>)
  ensures |result| == |a|
  ensures |a| == 0 ==> result == a
  ensures |a| > 0 ==> forall i :: 0 <= i < |a| ==> 
    result[i] == a[Mod(i - shift, |a|)]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): replaced loop with sequence constructor using lambda */
  if |a| == 0 {
    return a;
  } else {
    var n := |a|;
    var f := (i: nat) => a[Mod(i - shift, n)];
    return seq(n, f);
  }
}
// </vc-code>
