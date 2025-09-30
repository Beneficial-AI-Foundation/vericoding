// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function RealToString(r: real): string
{
  if r == 0.0 then "0" else "1"
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
    result := "[";
    var i := 0;
    while i < |a|
      invariant 0 <= i <= |a|
      invariant |result| > 0
      invariant result[0] == '['
    {
      var s := RealToString(a[i]);
      result := result + s;
      if i < |a| - 1 {
        result := result + ",";
      }
      i := i + 1;
    }
    result := result + "]";
  }
}
// </vc-code>
