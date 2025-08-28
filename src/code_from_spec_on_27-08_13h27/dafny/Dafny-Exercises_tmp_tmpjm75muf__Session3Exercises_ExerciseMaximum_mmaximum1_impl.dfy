//Algorithm 1: From left to right return the first

// <vc-helpers>
lemma MaximumProperty(v: array<int>, i: int)
  requires v.Length > 0
  requires 0 <= i < v.Length
  requires forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
// </vc-spec>
// </vc-spec>

// <vc-code>
method Maximum1(v: array<int>) returns (i: int)
  requires v.Length > 0
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
{
  i := 0;
  var maxVal := v[0];
  var j := 1;
  
  while j < v.Length
    invariant 0 <= i < v.Length
    invariant 0 <= j <= v.Length
    invariant maxVal == v[i]
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
  {
    if v[j] > maxVal {
      i := j;
      maxVal := v[j];
    }
    j := j + 1;
  }
}
// </vc-code>

//Algorithm 2: From right to left return the last




//Algorithm : from left to right
//Algorithm : from right to left