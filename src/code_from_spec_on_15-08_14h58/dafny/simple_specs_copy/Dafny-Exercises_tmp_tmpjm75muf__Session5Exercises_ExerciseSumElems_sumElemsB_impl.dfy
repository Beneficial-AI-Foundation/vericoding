//ATOM

function SumL(s:seq<int>):int
{
  if (s==[]) then 0
  else s[0]+SumL(s[1..])
}


//ATOM
function SumR(s:seq<int>):int
{
  if (s==[]) then 0
  else SumR(s[..|s|-1])+s[|s|-1]
}

/* code modified by LLM (iteration 1): Added helper lemma to prove relationship between SumR and appending elements */
lemma SumRAppend(s: seq<int>, x: int)
  ensures SumR(s + [x]) == SumR(s) + x
{
  if s == [] {
    assert s + [x] == [x];
    assert SumR([x]) == SumR([][..0]) + x == 0 + x == x;
    assert SumR(s) + x == 0 + x == x;
  } else {
    assert (s + [x])[..|s + [x]| - 1] == s[..|s|];
    assert (s + [x])[|s + [x]| - 1] == x;
    assert SumR(s + [x]) == SumR(s[..|s|]) + x == SumR(s) + x;
  }
}

//IMPL 

method sumElemsB(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[0..v.Length])
{
  sum := 0;
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[0..i])
  {
    /* code modified by LLM (iteration 1): Added assertion and lemma call to prove invariant maintenance */
    assert v[0..i+1] == v[0..i] + [v[i]];
    SumRAppend(v[0..i], v[i]);
    sum := sum + v[i];
    i := i + 1;
  }
}