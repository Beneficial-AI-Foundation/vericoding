// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate capturing no-duplicates up to prefix length j */
predicate NoDupsPrefix(s: seq<int>, j: int)
  requires 0 <= j <= |s|
{
  forall i:int, k:int :: 0 <= i < k < j ==> s[i] != s[k]
}

/* helper modified by LLM (iteration 5): extend no-duplicates prefix when current element is new */
lemma ExtendNoDupsWhenNew(s: seq<int>, j: int)
  requires 0 <= j < |s|
  requires NoDupsPrefix(s, j)
  requires forall a:int :: 0 <= a < j ==> s[a] != s[j]
  ensures NoDupsPrefix(s, j + 1)
{
  forall i:int, k:int | 0 <= i < k < j + 1
    ensures s[i] != s[k]
  {
    if k < j {
      assert 0 <= i < k < j;
      assert NoDupsPrefix(s, j);
      assert s[i] != s[k];
    } else {
      assert k == j;
      assert 0 <= i < j;
      assert s[i] != s[j];
    }
  }
}

/* helper modified by LLM (iteration 5): show that with a no-duplicate prefix up to j, any duplicate ending at or before i (< j) is impossible */
lemma ForallNoDuplicateUpToIndex(s: seq<int>, j: int, i: int)
  requires 0 <= i < j <= |s|
  requires NoDupsPrefix(s, j)
  ensures forall k:int, l:int :: 0 <= k < l < |s| && s[k] == s[l] && l <= i ==> k >= i
{
  forall k:int, l:int | 0 <= k < l < |s| && s[k] == s[l] && l <= i
    ensures k >= i
  {
    if k < i {
      assert l <= i < j;
      assert l < j;
      assert 0 <= k < l < j;
      assert NoDupsPrefix(s, j);
      assert s[k] != s[l];
      assert false;
    } else {
      assert k >= i;
    }
  }
}

// </vc-helpers>

// <vc-spec>
method FirstDuplicate(lst: seq<int>) returns (result: int)
    ensures
        /* if result = -1, then lst does not contain any duplicates */
        (result == -1 ==> forall i, j :: 0 <= i < j < |lst| ==> lst[i] != lst[j]) &&
        /* if result is not -1, then it is the first duplicate in lst */
        (result != -1 ==> 
            exists i, j :: (0 <= i < j < |lst| && lst[i] == lst[j] && lst[i] == result &&
            forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= i ==> k >= i))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): scan list to find first duplicate; ensure correctness via no-duplicate prefix lemmas */
  var n := |lst|;
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant NoDupsPrefix(lst, j)
    decreases n - j
  {
    var p := 0;
    var found := false;
    var w := 0;
    while p < j
      invariant 0 <= p <= j
      invariant NoDupsPrefix(lst, j)
      invariant (!found ==> forall a:int :: 0 <= a < p ==> lst[a] != lst[j])
      invariant (found ==> 0 <= w < p && lst[w] == lst[j])
      decreases j - p
    {
      if !found && lst[p] == lst[j] {
        found := true;
        w := p;
      }
      p := p + 1;
    }
    if found {
      result := lst[j];
      assert 0 <= w < j < n;
      assert lst[w] == lst[j];
      assert lst[w] == result;
      ForallNoDuplicateUpToIndex(lst, j, w);
      return;
    }
    if !found {
      assert forall a:int :: 0 <= a < j ==> lst[a] != lst[j];
      ExtendNoDupsWhenNew(lst, j);
    }
    j := j + 1;
  }
  assert NoDupsPrefix(lst, n);
  result := -1;
}

// </vc-code>
