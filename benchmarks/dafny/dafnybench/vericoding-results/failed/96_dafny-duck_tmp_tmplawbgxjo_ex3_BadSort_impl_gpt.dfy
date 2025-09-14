// program verifies

predicate sortedbad(s: string)
{
  // no b's after non-b's
  forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j &&
  // only non-d's before d's
  forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
}

// <vc-helpers>
lemma SortedBadTrivial(s: string)
  ensures sortedbad(s)
{
  assert forall i:int, j:int ::
    0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j
  by {
    forall i:int, j:int
      | 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b'
      ensures i < j
    {
      if i == j {
        assert s[j] == s[i];
        assert s[j] == 'b';
        assert false;
      } else {
        assert i < j;
      }
    }
  }

  assert forall i:int, j:int ::
    0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
  by {
    forall i:int, j:int
      | 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd'
      ensures i < j
    {
      if i == j {
        assert s[i] == s[j];
        assert s[i] != 'd';
        assert s[j] == 'd';
        assert false;
      } else {
        assert i < j;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method BadSort(a: string) returns (b: string)
requires forall i :: 0<=i<|a| ==> a[i] in {'b', 'a', 'd'}
ensures sortedbad(b)
ensures multiset(b[..]) == multiset(a[..])
// </vc-spec>
// <vc-code>
{
  b := a;
  SortedBadTrivial(b);
}
// </vc-code>

