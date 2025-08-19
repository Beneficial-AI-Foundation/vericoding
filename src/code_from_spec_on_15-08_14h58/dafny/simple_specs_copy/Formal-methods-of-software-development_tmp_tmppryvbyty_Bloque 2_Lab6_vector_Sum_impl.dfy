//ATOM
// SUM OF A SEQUENCE OF INTEGERS
function sum(v: seq<int>): int 
{
  if v==[] then 0
  else if |v|==1 then v[0]
  else v[0]+sum(v[1..])
}

/* code modified by LLM (iteration 2): added helper lemma for prefix sum property */
lemma sum_prefix_property(v: seq<int>, i: int)
  requires 0 <= i < |v|
  ensures sum(v[..i+1]) == sum(v[..i]) + v[i]
{
  if i == 0 {
    assert v[..1] == [v[0]];
    assert v[..0] == [];
    assert sum(v[..0]) == 0;
    assert sum(v[..1]) == v[0];
  } else {
    assert v[..i+1] == v[..i] + [v[i]];
    if |v[..i]| == 0 {
      assert sum(v[..i+1]) == sum([v[i]]) == v[i];
      assert sum(v[..i]) == 0;
    } else if |v[..i]| == 1 {
      assert sum(v[..i+1]) == v[0] + sum(v[1..i+1]);
      sum_prefix_property(v[1..], i-1);
    } else {
      assert sum(v[..i+1]) == v[0] + sum(v[1..i+1]);
      sum_prefix_property(v[1..], i-1);
      assert sum(v[1..i+1]) == sum(v[1..i]) + v[i];
      assert sum(v[..i]) == v[0] + sum(v[1..i]);
    }
  }
}

//IMPL 
method vector_Sum(v:seq<int>) returns (x:int)
ensures x == sum(v) 
{
  x := 0;
  var i := 0;
  while i < |v|
    invariant 0 <= i <= |v|
    invariant x == sum(v[..i])
  {
    /* code modified by LLM (iteration 2): use prefix sum property lemma */
    sum_prefix_property(v, i);
    assert sum(v[..i+1]) == sum(v[..i]) + v[i];
    assert x == sum(v[..i]);
    
    x := x + v[i];
    i := i + 1;
    
    /* code modified by LLM (iteration 2): assert loop invariant holds after update */
    assert x == sum(v[..i]);
  }
  
  /* code modified by LLM (iteration 2): assert postcondition after loop */
  assert i == |v|;
  assert v[..|v|] == v;
  assert x == sum(v[..|v|]);
}