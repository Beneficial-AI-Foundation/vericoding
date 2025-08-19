//ATOM
// SUM OF A SEQUENCE OF INTEGERS
function sum(v: seq<int>): int 
{
  if v==[] then 0
  else if |v|==1 then v[0]
  else v[0]+sum(v[1..])
}

/* code modified by LLM (iteration 1): added helper lemma to prove sum concatenation property */
lemma sum_concatenation(a: seq<int>, b: seq<int>)
  ensures sum(a + b) == sum(a) + sum(b)
{
  if a == [] {
    assert a + b == b;
  } else if |a| == 1 {
    calc {
      sum(a + b);
      == sum([a[0]] + b);
      == a[0] + sum(b);
      == sum(a) + sum(b);
    }
  } else {
    calc {
      sum(a + b);
      == (a + b)[0] + sum((a + b)[1..]);
      == a[0] + sum(a[1..] + b);
      == { sum_concatenation(a[1..], b); }
      a[0] + sum(a[1..]) + sum(b);
      == sum(a) + sum(b);
    }
  }
}

/* code modified by LLM (iteration 1): added helper lemma for single element sum */
lemma sum_single_element(x: int)
  ensures sum([x]) == x
{
  // This follows directly from the definition of sum
}

//IMPL 
method vector_Sum(v:seq<int>) returns (x:int)
ensures x == sum(v) 
{
  x := 0;
  var i := 0;
  while i < |v|
    invariant 0 <= i <= |v|
    invariant x == sum(v[0..i])
  {
    /* code modified by LLM (iteration 1): properly establish sequence equality and use helper lemmas */
    assert v[0..i+1] == v[0..i] + [v[i]];
    sum_concatenation(v[0..i], [v[i]]);
    assert sum(v[0..i+1]) == sum(v[0..i]) + sum([v[i]]);
    sum_single_element(v[i]);
    assert sum([v[i]]) == v[i];
    
    x := x + v[i];
    i := i + 1;
  }
}