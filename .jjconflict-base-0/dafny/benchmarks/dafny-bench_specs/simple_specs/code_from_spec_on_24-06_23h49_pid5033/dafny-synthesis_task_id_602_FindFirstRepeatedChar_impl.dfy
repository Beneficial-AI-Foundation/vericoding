//IMPL 
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
  ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
{
  found := false;
  c := '\0';
  
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant !found ==> (forall p, q :: 0 <= p < q < |s| && (p < i || (p == i && q <= i)) ==> s[p] != s[q])
    /* code modified by LLM (iteration 2): Updated invariant to be more precise about what we've checked */
    invariant found ==> exists p, q :: 0 <= p < q < |s| && s[p] == s[q] && s[p] == c && (forall k, l :: 0 <= k < l < q && s[k] == s[l] ==> k >= p)
  {
    var j := i + 1;
    while j < |s|
      invariant i < j <= |s|
      invariant !found ==> (forall p, q :: 0 <= p < q < |s| && (p < i || (p == i && q < j)) ==> s[p] != s[q])
      /* code modified by LLM (iteration 2): More precise invariant about what pairs we've checked */
      invariant found ==> exists p, q :: 0 <= p < q < |s| && s[p] == s[q] && s[p] == c && (forall k, l :: 0 <= k < l < q && s[k] == s[l] ==> k >= p)
    {
      if s[i] == s[j] && !found {
        /* code modified by LLM (iteration 2): Added lemma call to prove the minimality property */
        ProveMinimality(s, i, j);
        found := true;
        c := s[i];
        break;
      }
      j := j + 1;
    }
    if found {
      break;
    }
    i := i + 1;
  }
}

/* code modified by LLM (iteration 2): Added helper lemma to prove minimality */
lemma ProveMinimality(s: string, i: int, j: int)
  requires 0 <= i < j < |s|
  requires s[i] == s[j]
  requires forall p, q :: 0 <= p < q < |s| && (p < i || (p == i && q < j)) ==> s[p] != s[q]
  ensures forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i
{
  /* code modified by LLM (iteration 2): Proof by contradiction */
  forall k, l | 0 <= k < l < j && s[k] == s[l]
    ensures k >= i
  {
    if k < i {
      assert 0 <= k < l < |s| && (k < i || (k == i && l < j));
      assert s[k] != s[l]; // contradiction
    }
  }
}