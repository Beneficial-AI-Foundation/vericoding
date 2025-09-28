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
  /* code modified by LLM (iteration 3): implemented loop with proper invariants to ensure length and content */
  if |a| == 0 {
    result := a;
  } else {
    var n := |a|;
    result := [];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> result[j] == a[Mod(j - shift, n)]
    {
      var idx := Mod(i - shift, n);
      result := result + [a[idx]];
      i := i + 1;
    }
  }
}
// </vc-code>
