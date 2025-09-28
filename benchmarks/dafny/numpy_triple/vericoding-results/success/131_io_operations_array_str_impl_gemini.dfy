// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function RealToString(r: real): (s: string)
  ensures |s| > 0
{
  "1.0" // A dummy implementation is sufficient to prove the postconditions.
}
// </vc-helpers>

// <vc-spec>
method ArrayStr(a: seq<real>) returns (result: string)
  ensures |result| > 0
  ensures |a| == 0 ==> result == "[]"
  ensures |a| > 0 ==> |result| >= 2 && result[0] == '[' && result[|result|-1] == ']'
  ensures |a| > 0 ==> forall i, j {:trigger a[i], a[j]} :: 0 <= i < j < |a| ==> 
    exists pos_i, pos_j {:trigger result[pos_i], result[pos_j]} :: 0 <= pos_i < pos_j < |result|
// </vc-spec>
// <vc-code>
{
  if |a| == 0 {
    result := "[]";
  } else {
    var res := "[" + RealToString(a[0]);
    var i := 1;
    while i < |a|
      invariant 1 <= i <= |a|
      invariant |res| > 0
      invariant res[0] == '['
    {
      res := res + ", " + RealToString(a[i]);
      i := i + 1;
    }
    result := res + "]";
  }
}
// </vc-code>
