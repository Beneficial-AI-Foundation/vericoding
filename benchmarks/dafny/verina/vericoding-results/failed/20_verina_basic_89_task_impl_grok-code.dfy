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
/* code modified by LLM (iteration 5): removed global var causing compilation error, fixed uniqueness impl with set for efficiency */
var res: seq<int> := [];
var unique: set<int> := {};
var i := 0;
while i < |s|
  invariant 0 <= i <= |s|
  invariant forall k :: 0 <= k < i ==> s[k] in unique
  invariant |unique| == |res|
  invariant forall k, l :: 0 <= k < l < |res| ==> res[k] != res[l]
  invariant forall x :: x in unique <==> x in res
  invariant forall x :: x in unique ==> exists k :: 0 <= k < i && s[k] == x
{
  if !(s[i] in unique) {
    unique := unique + {s[i]};
    res := res + [s[i]];
  }
  i := i + 1;
}
result := res;
}
// </vc-code>
