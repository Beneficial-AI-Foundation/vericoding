//Algorithm 1: From left to right return the first

//Algorithm 2: From right to left return the last

// <vc-helpers>
// No helper updates needed
// </vc-helpers>

// <vc-spec>
method mlastMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: i<l<v.Length ==> v[i]>v[l]
// </vc-spec>
// <vc-code>
{
  var n := v.Length;
  var idx := n - 1;
  var j := n - 1;
  while j > 0
    invariant 0 <= j < n
    invariant j <= idx < n
    invariant forall k :: j <= k < n ==> v[idx] >= v[k]
    invariant forall l :: idx < l < n ==> v[idx] > v[l]
    decreases j
  {
    var k := j - 1;
    if v[k] > v[idx] {
      var oldIdx := idx;
      assert forall t :: j <= t < n ==> v[oldIdx] >= v[t];
      idx := k;
      assert v[idx] > v[oldIdx];
      forall t | k <= t && t < n
        ensures v[idx] >= v[t]
      {
        if t == k {
          assert v[idx] >= v[t];
        } else {
          assert t > k;
          assert k == j - 1;
          assert t >= j;
          assert v[oldIdx] >= v[t];
          assert v[idx] > v[oldIdx];
          assert v[idx] > v[t];
        }
      }
      forall l | idx < l && l < n
        ensures v[idx] > v[l]
      {
        assert idx == k;
        assert l > k;
        assert k == j - 1;
        assert l >= j;
        assert v[oldIdx] >= v[l];
        assert v[idx] > v[oldIdx];
        assert v[idx] > v[l];
      }
    } else {
      assert v[idx] >= v[k];
      forall t | k <= t && t < n
        ensures v[idx] >= v[t]
      {
        if t == k {
          assert v[idx] >= v[t];
        } else {
          assert t > k;
          assert k == j - 1;
          assert t >= j;
          assert v[idx] >= v[t];
        }
      }
    }
    j := k;
  }
  return idx;
}
// </vc-code>

//Algorithm : from left to right
//Algorithm : from right to left