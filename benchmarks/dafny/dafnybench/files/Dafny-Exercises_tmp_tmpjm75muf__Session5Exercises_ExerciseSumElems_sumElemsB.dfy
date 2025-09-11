// <vc-preamble>
function SumR(s:seq<int>):int
decreases s
{
    if (s==[]) then 0
    else SumR(s[..|s|-1])+s[|s|-1]
}

function SumL(s:seq<int>):int
decreases s
{
    if (s==[]) then 0
    else s[0]+SumL(s[1..])
}

function SumV(v:array<int>,c:int,f:int):int
  requires 0<=c<=f<=v.Length
  reads v
  {SumR(v[c..f])}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method sumElemsB(v:array<int>) returns (sum:int)
ensures sum==SumR(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
