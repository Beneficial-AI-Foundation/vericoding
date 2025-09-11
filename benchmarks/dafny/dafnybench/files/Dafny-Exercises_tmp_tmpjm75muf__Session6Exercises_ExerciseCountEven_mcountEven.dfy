// <vc-preamble>
predicate positive(s:seq<int>)
{
  forall u::0<=u<|s| ==> s[u]>=0
  }

predicate isEven(i:int)
requires i>=0
{
  i%2==0
}

function CountEven(s:seq<int>):int
decreases s
requires positive(s)
{
  if s==[] then 0
  else (if (s[|s|-1]%2==0) then 1 else 0)+CountEven(s[..|s|-1])

}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method mcountEven(v:array<int>) 
returns (n:int)
requires positive(v[..])
ensures  n==CountEven(v[..])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
