predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

// <vc-helpers>
lemma negativeElementMakesPositiveFalse(s: seq<int>, i: int)
  requires 0 <= i < |s|
  requires s[i] < 0
  ensures !positive(s)
{
  // The existence of a negative element at index i proves positive(s) is false
}
// </vc-helpers>

// <vc-spec>
method mpositive3(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant forall k :: 0 <= k < i ==> v[k] >= 0
  {
    if v[i] < 0 {
      negativeElementMakesPositiveFalse(v[0..v.Length], i);
      b := false;
      return;
    }
    i := i + 1;
  }
  b := true;
}
// </vc-code>