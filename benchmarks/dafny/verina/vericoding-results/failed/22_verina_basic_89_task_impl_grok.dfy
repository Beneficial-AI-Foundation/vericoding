// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SetToSeq(s: seq<int>) returns (result: seq<int>)
    ensures
        // All elements are unique in the result  
        forall i: int, j: int :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures
        // Every element in result is in s
        forall i: int :: 0 <= i < |result| ==> 
            exists j: int :: 0 <= j < |s| && s[j] == result[i]
    ensures
        // Every element in s is in result
        forall i: int :: 0 <= i < |s| ==> 
            exists j: int :: 0 <= j < |result| && result[j] == s[i]
// </vc-spec>
// <vc-code>
{
  var seen: set<int> := {};
  var res: seq<int> := [];
  var i: nat := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant seen == (set x | x in res :: x)
    invariant forall j :: 0 <= j < i ==> s[j] in seen
    invariant forall x :: x in seen ==> exists j :: 0 <= j < i && s[j] == x
    invariant forall k1, k2 :: 0 <= k1 < k2 < |res| ==> res[k1] != res[k2]
  {
    if s[i] !in seen {
      res := res + [s[i]];
      seen := seen + {s[i]};
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>
