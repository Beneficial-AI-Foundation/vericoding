function SumL(s:seq<int>):int
{
  if (s==[]) then 0
  else s[0]+SumL(s[1..])
}


//ATOM


function SumV(v:array<int>,c:int,f:int):int
 requires 0<=c<=f<=v.Length
 reads v
 {SumR(v[c..f])}


//ATOM
function SumR(s:seq<int>):int
{
  if (s==[]) then 0
  else SumR(s[..|s|-1])+s[|s|-1]
}

lemma SumRExtend(s: seq<int>, x: int)
  ensures SumR(s + [x]) == SumR(s) + x
{
  if s == [] {
    assert s + [x] == [x];
    /* code modified by LLM (iteration 1): Fixed type cast by using proper empty sequence literal */
    var empty: seq<int> := [];
    assert SumR([x]) == SumR(empty) + x == 0 + x == x;
  } else {
    assert (s + [x])[..|s + [x]| - 1] == s;
    assert (s + [x])[|s + [x]| - 1] == x;
  }
}

//IMPL
method sumElems(v:array<int>) returns (sum:int)
ensures sum==SumR(v[..])
{
  sum := 0;
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[..i])
  {
    SumRExtend(v[..i], v[i]);
    assert v[..i] + [v[i]] == v[..i+1];
    sum := sum + v[i];
    i := i + 1;
  }
}