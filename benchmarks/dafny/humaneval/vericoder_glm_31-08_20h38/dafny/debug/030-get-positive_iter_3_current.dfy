

// <vc-helpers>
function method get_positive_sub(s: seq<int>): seq<int>
    decreases |s|
{
    if |s| == 0 then []
    else if s[0] > 0 then [s[0]] + get_positive_sub(s[1..])
    else get_positive_sub(s[1..])
}
// </vc-helpers>

// <vc-spec>
method get_positive(l : seq<int>) returns (result : seq<int>)
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |result| ==> result[i] > 0
    ensures |result| <= |l|
    ensures forall i1 :: i1 >= 0 && i1 < |l| ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
    ensures |result| == 0 || (forall i1 : int :: i1 >= 0 && i1 < |result| ==> (exists i2 :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i: int := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant res == get_positive_sub(l[0..i])
  {
    if l[i] > 0
    {
      res := res + [l[i]];
    }
    i := i + 1;
  }
  return res;
}
// </vc-code>

