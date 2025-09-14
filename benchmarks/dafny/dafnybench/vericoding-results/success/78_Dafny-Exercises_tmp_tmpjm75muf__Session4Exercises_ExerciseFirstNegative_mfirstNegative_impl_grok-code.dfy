predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mfirstNegative(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists k::0<=k<v.Length && v[k]<0
ensures b ==> 0<=i<v.Length && v[i]<0 && positive(v[0..i])
// </vc-spec>
// <vc-code>
{
  var j := 0;
  b := false;
  i := 0;
  while j < v.Length
    invariant 0 <= j <= v.Length
    invariant b ==> 0 <= i < j && v[i] < 0 && positive(v[0..i])
    invariant !b ==> forall k :: 0 <= k < j ==> v[k] >= 0
  {
    if v[j] < 0 {
      b := true;
      i := j;
      break;
    }
    j := j + 1;
  }
}
// </vc-code>

