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
/* helper modified by LLM (iteration 2): dummy helper retained for verification structure */
lemma DummyHelper() ensures true {
}

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
  /* code modified by LLM (iteration 2): build result sequence iteratively to avoid creating new T[n] array */
  var n := |a|;
  if n == 0 {
    result := a;
  } else {
    var res: seq<T> := [];
    var k := 0;
    while k < n
      invariant 0 <= k <= n
      invariant |res| == k
      invariant forall i :: 0 <= i < k ==> res[i] == a[Mod(i - shift, n)]
    {
      res := res + [a[Mod(k - shift, n)]];
      k := k + 1;
    }
    result := res;
  }
}

// </vc-code>
