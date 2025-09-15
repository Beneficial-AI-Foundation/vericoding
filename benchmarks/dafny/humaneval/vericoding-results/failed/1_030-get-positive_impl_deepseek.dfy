// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function filterPositive(s: seq<int>): (r: seq<int>)
  ensures forall i :: 0 <= i < |r| ==> r[i] > 0
  ensures |r| <= |s|
  ensures forall i :: 0 <= i < |s| ==> (s[i] > 0 ==> exists j :: 0 <= j < |r| && r[j] == s[i])
  ensures |r| == 0 || (forall i :: 0 <= i < |r| ==> exists j :: 0 <= j < |s| && s[j] == r[i])
{
  if |s| == 0 then
    []
  else
    var rest := filterPositive(s[1..]);
    if s[0] > 0 then
      [s[0]] + rest
    else
      rest
}
// </vc-helpers>

// <vc-spec>
method get_positive(l : seq<int>) returns (result : seq<int>)

    ensures forall i : int :: i >= 0 && i < |result| ==> result[i] > 0
    ensures |result| <= |l|
    ensures forall i1 :: i1 >= 0 && i1 < |l| ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
    ensures |result| == 0 || (forall i1 : int :: i1 >= 0 && i1 < |result| ==> (exists i2 :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Direct implementation with loop */
  result := [];
  var index := 0;
  while index < |l|
    invariant 0 <= index <= |l|
    invariant forall i :: 0 <= i < |result| ==> result[i] > 0
    invariant |result| <= index
    invariant forall i :: 0 <= i < index ==> (l[i] > 0 ==> exists j :: 0 <= j < |result| && result[j] == l[i])
    invariant |result| == 0 || (forall i :: 0 <= i < |result| ==> exists j :: 0 <= j < index && l[j] == result[i])
  {
    if l[index] > 0 {
      result := result + [l[index]];
    }
    index := index + 1;
  }
}
// </vc-code>
