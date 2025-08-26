method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
// </vc-spec>
// <vc-code>
{
  found := false;
  c := ' '; // dummy value
  
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant !found ==> (forall k, l :: 0 <= k < l <= i ==> s[k] != s[l])
    invariant found ==> exists p, q :: 0 <= p < q < |s| && s[p] == s[q] && s[p] == c && (forall k, l :: 0 <= k < l < q && s[k] == s[l] ==> k >= p)
  {
    var j := i + 1;
    while j < |s|
      invariant i < j <= |s|
      invariant forall k :: i < k < j ==> s[i] != s[k]
      invariant !found ==> (forall k, l :: 0 <= k < l <= i ==> s[k] != s[l])
      invariant found ==> exists p, q :: 0 <= p < q < |s| && s[p] == s[q] && s[p] == c && (forall k, l :: 0 <= k < l < q && s[k] == s[l] ==> k >= p)
    {
      if s[i] == s[j] {
        found := true;
        c := s[i];
        
        // Prove the postcondition
        assert 0 <= i < j < |s| && s[i] == s[j] && s[i] == c;
        
        // Prove that this is the first occurrence
        forall k, l | 0 <= k < l < j && s[k] == s[l]
          ensures k >= i
        {
          if l <= i {
            // We know no repetitions exist in [0, i]
            assert s[k] != s[l]; // contradiction
          } else {
            // l is in (i, j), so s[i] != s[l] by inner loop invariant
            // But s[i] == s[j], so if s[k] == s[l] and we want k >= i
            if k < i {
              // We have s[k] == s[l] where k < i < l < j
              // But we know no repetitions in [0, i], and s[i] != s[l]
              // This case needs careful analysis
              assert k < i <= l;
              if l == i {
                assert s[k] == s[i];
                assert k < i;
                assert false; // contradicts no repetitions in [0, i]
              } else {
                assert i < l < j;
                assert s[i] != s[l]; // from inner loop invariant
                // This is allowed, but k must be >= i is what we want to prove
                // Actually, this case is fine - we don't have a contradiction
                // We need to be more careful about the first occurrence property
              }
            }
          }
        }
        
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

// <vc-helpers>
// </vc-helpers>