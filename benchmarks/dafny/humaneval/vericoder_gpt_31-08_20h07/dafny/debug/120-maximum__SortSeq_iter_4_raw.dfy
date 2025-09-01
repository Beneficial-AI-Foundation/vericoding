```vc-helpers
lemma {:axiom} ExistsSortedPermutation(s: seq<int>)
  ensures exists t: seq<int> ::
    (forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]) &&
    |t| == |s| &&
    multiset(s) == multiset(t) &&
    (forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |t| && s[i] == t[j]) &&
    (forall x :: x in s ==> x in t) &&
    (forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |t| && t[i] == s[j]) &&
    (forall x :: x in t ==> x in s)
```

```vc-code
{
  ExistsSortedPermutation(s);
  var sr: seq<int> :|
    (forall i, j :: 0 <= i < j < |sr| ==> sr[i] <= sr[j]) &&
    |sr| == |s| &&
    multiset(s) == multiset(sr) &&
    (forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sr| && s[i] == sr[j]) &&
    (forall x :: x in s ==> x in sr) &&
    (forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sr| && sr[i] == s[j]) &&
    (forall x :: x in sr ==> x in s);
  sorted := sr;
}
```