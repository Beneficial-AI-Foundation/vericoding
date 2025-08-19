//ATOM
// SUM OF A SEQUENCE OF INTEGERS
function sum(v: seq<int>): int 
{
  if v==[] then 0
  else if |v|==1 then v[0]
  else v[0]+sum(v[1..])
}

//IMPL vector_Sum
method vector_Sum(v:seq<int>) returns (x:int)
ensures x == sum(v) 
{
  x := 0;
  var i := 0;
  while i < |v|
    invariant 0 <= i <= |v|
    invariant x == sum(v[..i])
  {
    /* code modified by LLM (iteration 1): Added assertion to help prove loop invariant maintenance */
    assert v[..i+1] == v[..i] + [v[i]];
    /* code modified by LLM (iteration 1): Added lemma call to establish sum property */
    sum_prefix_lemma(v, i);
    x := x + v[i];
    i := i + 1;
  }
  /* code modified by LLM (iteration 1): Added assertion to help prove postcondition */
  assert i == |v|;
  assert v[..i] == v;
}

/* code modified by LLM (iteration 1): Added helper lemma to prove sum properties */
lemma sum_prefix_lemma(v: seq<int>, i: int)
  requires 0 <= i < |v|
  ensures sum(v[..i+1]) == sum(v[..i]) + v[i]
{
  if i == 0 {
    assert v[..1] == [v[0]];
    assert sum(v[..1]) == v[0];
    assert sum(v[..0]) == sum([]) == 0;
  } else {
    assert v[..i+1] == v[..i] + [v[i]];
    sum_concat_lemma(v[..i], [v[i]]);
  }
}

/* code modified by LLM (iteration 1): Added helper lemma for sum concatenation */
lemma sum_concat_lemma(a: seq<int>, b: seq<int>)
  ensures sum(a + b) == sum(a) + sum(b)
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert (a + b)[0] == a[0];
    assert (a + b)[1..] == a[1..] + b;
    sum_concat_lemma(a[1..], b);
  }
}