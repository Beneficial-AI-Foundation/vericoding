

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Filter(a:seq<char>, b:set<char>) returns(c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
// </vc-spec>
// <vc-code>
{
  var result: set<char> := {};
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall x :: x in result ==> x in a[..i] && x in b
    invariant forall x :: (exists k :: 0 <= k < i && a[k] == x && x in b) ==> x in result
  {
    if a[i] in b {
      result := result + {a[i]};
    }
    i := i + 1;
  }
  return result;
}
// </vc-code>

