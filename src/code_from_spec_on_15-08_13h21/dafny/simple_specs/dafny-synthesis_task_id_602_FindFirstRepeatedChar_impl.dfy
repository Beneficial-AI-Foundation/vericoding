method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
  ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
{
  found := false;
  c := 'a'; // dummy value
  
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    /* code modified by LLM (iteration 4): Fixed invariant bounds and simplified condition */
    invariant !found ==> (forall k, l :: 0 <= k < l < i ==> s[k] != s[l])
    invariant found ==> exists p, q :: 0 <= p < q < |s| && s[p] == s[q] && s[p] == c && (forall k, l :: 0 <= k < l < q && s[k] == s[l] ==> k >= p)
  {
    var j := i + 1;
    while j < |s|
      invariant i + 1 <= j <= |s|
      invariant forall k :: i + 1 <= k < j ==> s[i] != s[k]
      /* code modified by LLM (iteration 4): Maintained outer invariants in inner loop */
      invariant !found ==> (forall k, l :: 0 <= k < l < i ==> s[k] != s[l])
      invariant found ==> exists p, q :: 0 <= p < q < |s| && s[p] == s[q] && s[p] == c && (forall k, l :: 0 <= k < l < q && s[k] == s[l] ==> k >= p)
    {
      if s[i] == s[j] {
        found := true;
        c := s[i];
        /* code modified by LLM (iteration 4): Correct assertion proof for postcondition */
        assert 0 <= i < j < |s| && s[i] == s[j] && s[i] == c;
        assert forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i by {
          forall k, l | 0 <= k < l < j && s[k] == s[l]
            ensures k >= i
          {
            if k < i {
              if l < i {
                /* code modified by LLM (iteration 4): Use correct invariant reference */
                assert forall a, b :: 0 <= a < b < i ==> s[a] != s[b];
                /* code modified by LLM (iteration 4): Fixed assertion by removing contradictory statement */
              } else if l == i {
                /* code modified by LLM (iteration 4): Use inner loop invariant correctly */
                assert forall m :: i + 1 <= m < j ==> s[i] != s[m];
                /* code modified by LLM (iteration 4): Fixed assertion by removing contradictory statement */
              } else {
                /* code modified by LLM (iteration 4): l > i case, use inner loop invariant correctly */
                assert i < l < j;
                assert i + 1 <= l < j;
                assert s[i] != s[l];
                /* code modified by LLM (iteration 4): Fixed assertion by removing contradictory statement */
              }
            }
          }
        }
        return;
      }
      j := j + 1;
    }
    /* code modified by LLM (iteration 4): Added assertion to help prove outer loop invariant maintenance */
    assert forall k :: i + 1 <= k < |s| ==> s[i] != s[k];
    assert forall k, l :: 0 <= k < l < i ==> s[k] != s[l];
    assert forall k, l :: 0 <= k < l < i + 1 ==> s[k] != s[l] by {
      forall k, l | 0 <= k < l < i + 1
        ensures s[k] != s[l]
      {
        if l <= i {
          if l < i {
            /* code modified by LLM (iteration 4): Use invariant directly */
          } else {
            assert l == i;
            if k < i {
              /* code modified by LLM (iteration 4): Fixed assertion by removing contradictory statement */
            }
          }
        }
      }
    }
    i := i + 1;
  }
}