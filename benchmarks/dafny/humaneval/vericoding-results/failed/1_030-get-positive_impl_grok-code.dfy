// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added recursive function to compute the sequence of positive elements. */
function GetPositive(l: seq<int>): (result: seq<int>)
ensures forall i: int :: i >= 0 && i < |result| ==> result[i] > 0
ensures |result| <= |l|
ensures forall i1 :: i1 >= 0 && i1 < |l| ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
ensures |result| == 0 || (forall i1: int :: i1 >= 0 && i1 < |result| ==> (exists i2 :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]))
{
  if |l| == 0 then []
  else if l[0] > 0 then [l[0]] + GetPositive(l[1..])
  else GetPositive(l[1..])
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
  /* code modified by LLM (iteration 5): Call the recursive function to get the result. */
  result := GetPositive(l);
}
// </vc-code>
