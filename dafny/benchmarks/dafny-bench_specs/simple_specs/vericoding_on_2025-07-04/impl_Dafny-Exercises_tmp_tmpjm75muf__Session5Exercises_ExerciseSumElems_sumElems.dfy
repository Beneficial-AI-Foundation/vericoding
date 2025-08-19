//ATOM

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


//IMPL

/* code modified by LLM (iteration 2): helper lemma to establish SumR property for array slices */
lemma SumRArraySlice(v: array<int>, i: int)
  requires 0 < i <= v.Length
  ensures SumR(v[i-1..]) == SumR(v[i..]) + v[i-1]
{
  var fullSlice := v[i-1..];
  var restSlice := v[i..];
  
  assert fullSlice == [v[i-1]] + restSlice;
  assert |fullSlice| > 0;
  assert fullSlice[|fullSlice|-1] == v[v.Length-1];
  assert fullSlice[..|fullSlice|-1] == restSlice;
  
  calc {
    SumR(v[i-1..]);
    SumR(fullSlice);
    SumR(fullSlice[..|fullSlice|-1]) + fullSlice[|fullSlice|-1];
    SumR(restSlice) + v[i-1];
    SumR(v[i..]) + v[i-1];
  }
}

method sumElems(v:array<int>) returns (sum:int)
ensures sum==SumR(v[..])
{
  sum := 0;
  var i := v.Length;
  
  while i > 0
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[i..])
  {
    /* code modified by LLM (iteration 2): apply lemma before updating variables */
    SumRArraySlice(v, i);
    
    i := i - 1;
    sum := sum + v[i];
  }
}