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
  var max_index := 0;
  var max_value := v[0];
  var j := 1;
  while (j < v.Length)
    invariant 0 <= j <= v.Length
    invariant 0 <= max_index < v.Length
    invariant max_value == v[max_index]
    invariant forall k :: 0 <= k < j ==> max_value >= v[k]
  {
    if (v[j] > max_value) {
      max_value := v[j];
      max_index := j;
    }
    j := j + 1;
  }
  return max_index;
}
// </vc-code>

//Algorithm 2: From right to left return the last




//Algorithm : from left to right
//Algorithm : from right to left