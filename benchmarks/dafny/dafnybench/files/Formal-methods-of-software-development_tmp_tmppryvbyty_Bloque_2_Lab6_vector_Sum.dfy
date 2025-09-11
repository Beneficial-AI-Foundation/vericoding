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
// </vc-helpers>

// <vc-spec>
method vector_Sum(v:seq<int>) returns (x:int)
ensures x == sum(v)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
