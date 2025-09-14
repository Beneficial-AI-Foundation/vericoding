//Algorithm 1: From left to right return the first

//Algorithm 2: From right to left return the last

// <vc-helpers>
lemma gt_trans_ge(x:int, y:int, z:int)
  requires x > y
  requires y >= z
  ensures x > z
{}
// </vc-helpers>

// <vc-spec>
method mfirstMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: 0<=l<i ==> v[i]>v[l]
//Algorithm: from left to right
// </vc-spec>
// <vc-code>
{
  var n := v.Length;
  var best := 0;
  var j := 1;
  while j < n
    invariant 1 <= j <= n
    invariant 0 <= best < j
    invariant forall k :: 0 <= k < j ==> v[best] >= v[k]
    invariant forall l :: 0 <= l < best ==> v[best] > v[l]
    decreases n - j
  {
    if v[j] > v[best] {
      forall l | 0 <= l < j
        ensures v[j] > v[l]
      {
        assert v[best] >= v[l];
        gt_trans_ge(v[j], v[best], v[l]);
      }
      best := j;
    }
    j := j + 1;
  }
  i := best;
}
// </vc-code>

//Algorithm : from left to right
//Algorithm : from right to left