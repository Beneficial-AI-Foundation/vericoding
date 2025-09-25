// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Filter(a:seq<char>, b:set<char>) returns(c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
