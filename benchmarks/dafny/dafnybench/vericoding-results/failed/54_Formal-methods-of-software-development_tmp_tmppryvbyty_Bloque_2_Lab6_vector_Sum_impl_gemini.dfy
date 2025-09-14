// <vc-preamble>
function sum(v: seq<int>): int 
decreases v
{
    if v==[] then 0
    else if |v|==1 then v[0]
    else v[0]+sum(v[1..])
}

function reverse<T> (s:seq<T>):seq<T> 
{
    if s==[] then []
    else reverse(s[1..])+[s[0]]
}

function seq2set<T> (s:seq<T>): set<T>
{
    if s==[] then {}
    else {s[0]}+seq2set(s[1..])
}

function scalar_product (v1:seq<int>, v2:seq<int>):int
requires |v1| == |v2|
{
    if v1 == [] then 0 else v1[0]*v2[0] + scalar_product(v1[1..],v2[1..])
}

method multiplicity_examples<T> ()
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simplified lemma structure */
lemma sum_append_lemma(s: seq<int>, a: int)
  ensures sum(s + [a]) == sum(s) + a
  decreases s
{
  if s != [] {
    sum_append_lemma(s[1..], a);
  }
}
// </vc-helpers>

// <vc-spec>
method vector_Sum(v:seq<int>) returns (x:int)
ensures x == sum(v)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): add lemma call before update */
  x := 0;
  var i := 0;
  while i < |v|
    invariant 0 <= i <= |v|
    invariant x == sum(v[0..i])
  {
    sum_append_lemma(v[0..i], v[i]);
    x := x + v[i];
    i := i + 1;
  }
}
// </vc-code>
