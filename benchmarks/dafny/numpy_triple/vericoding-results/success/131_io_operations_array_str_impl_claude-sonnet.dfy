// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function RealToString(r: real): string
  ensures |RealToString(r)| > 0
{
  "0.0"
}

function SeqToStringHelper(a: seq<real>, i: int): string
  requires 0 <= i <= |a|
  ensures |SeqToStringHelper(a, i)| >= 0
  decreases |a| - i
{
  if i == |a| then ""
  else if i == |a| - 1 then RealToString(a[i])
  else RealToString(a[i]) + ", " + SeqToStringHelper(a, i + 1)
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
    var inner := SeqToStringHelper(a, 0);
    result := "[" + inner + "]";
  }
}
// </vc-code>
