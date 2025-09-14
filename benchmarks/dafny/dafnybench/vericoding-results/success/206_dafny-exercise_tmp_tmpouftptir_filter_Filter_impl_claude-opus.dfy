

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Filter(a:seq<char>, b:set<char>) returns(c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
// </vc-spec>
// <vc-code>
{
  c := {};
  for i := 0 to |a|
    invariant forall x :: x in a[..i] && x in b <==> x in c
  {
    if a[i] in b {
      c := c + {a[i]};
    }
  }
}
// </vc-code>

