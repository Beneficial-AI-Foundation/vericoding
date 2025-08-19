
// <vc-dependencies>
predicate valid_bitvec(v: seq<int>)
{
  forall i :: 0 <= i < |v| ==> (v[i] == 0 || v[i] == 1)
}

ghost function vec2int(v: seq<int>): int
  decreases |v|
{
  if |v| == 0 then 0 
  else v[0] + 2 * vec2int(v[1..])
}
// </vc-dependencies>

// <vc-task>
method add(v1: seq<int>, v2: seq<int>) returns (result: seq<int>)
  requires valid_bitvec(v1) && valid_bitvec(v2)
  ensures valid_bitvec(result)
  ensures vec2int(result) == vec2int(v1) + vec2int(v2)
{
  assume false;
}
// </vc-task>




