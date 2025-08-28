//Algorithm 1: From left to right return the first

//Algorithm 2: From right to left return the last

// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mfirstMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: 0<=l<i ==> v[i]>v[l]
//Algorithm: from left to right
// </vc-spec>
// </vc-spec>

// <vc-code>
method mfirstMaximum(v: array<int>) returns (i: int)
  requires v.Length > 0
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
  ensures forall l :: 0 <= l < i ==> v[i] > v[l]
{
  i := 0;
  var maxVal := v[0];
  var j := 1;
  
  while j < v.Length
    invariant 0 <= i < j <= v.Length
    invariant maxVal == v[i]
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
    invariant forall l :: 0 <= l < i ==> v[i] > v[l]
  {
    if v[j] > maxVal {
      i := j;
      maxVal := v[j];
    }
    j := j + 1;
  }
}
// </vc-code>

//Algorithm : from left to right
//Algorithm : from right to left