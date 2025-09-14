

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Filter(a:seq<char>, b:set<char>) returns(c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
// </vc-spec>
// <vc-code>
{
  var s: set<char> := {};
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant forall x :: x in s <==> (exists k :: 0 <= k < i && a[k] == x && x in b)
  {
    if i < |a| && a[i] in b { // Added i < |a| to prevent out-of-bounds access
      s := s + {a[i]};
    }
  }
  return s;
}
// </vc-code>

