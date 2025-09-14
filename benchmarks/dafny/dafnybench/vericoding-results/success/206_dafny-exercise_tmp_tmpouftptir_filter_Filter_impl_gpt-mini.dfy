

// <vc-helpers>
// No helper functions required.
// </vc-helpers>

// <vc-spec>
method Filter(a:seq<char>, b:set<char>) returns(c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
// </vc-spec>
// <vc-code>
{
  c := set x | x in a && x in b;
}
// </vc-code>

