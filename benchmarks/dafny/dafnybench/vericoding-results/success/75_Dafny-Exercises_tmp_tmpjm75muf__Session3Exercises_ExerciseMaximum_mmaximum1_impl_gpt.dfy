//Algorithm 1: From left to right return the first

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
// </vc-spec>
// <vc-code>
{
  var idx := 0;
  var m := v[0];
  var t := 1;
  while t < v.Length
    invariant 1 <= t <= v.Length
    invariant 0 <= idx < t
    invariant m == v[idx]
    invariant forall k :: 0 <= k < t ==> v[idx] >= v[k]
    decreases v.Length - t
  {
    if v[t] > m {
      idx := t;
      m := v[t];
    }
    t := t + 1;
  }
  i := idx;
}
// </vc-code>

//Algorithm 2: From right to left return the last




//Algorithm : from left to right
//Algorithm : from right to left