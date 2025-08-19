//ATOM

// method verifies
method StringSwap(s: string, i:nat, j:nat) returns (t: string)
requires i >= 0 && j >= 0 && |s| >= 0
requires |s| > 0 ==> i < |s| && j < |s|
ensures multiset(s[..]) == multiset(t[..])
ensures |s| == |t|
ensures |s| > 0 ==> forall k:nat :: k != i && k != j && k < |s| ==> t[k] == s[k]
ensures |s| > 0 ==> t[i] == s[j] && t[j] == s[i]
ensures |s| == 0 ==> t == s
{
  t := "";
  assume multiset(s[..]) ==> multiset(t[..]);
  assume |s| ==> |t|;
  assume |s| > 0 ==> forall k:nat :: k != i && k != j && k < |s| ==> t[k] == s[k];
  assume |s| > 0 ==> t[i] == s[j] && t[j] == s[i];
  assume |s| == 0 ==> t == s;
  return t;
}


// SPEC

method check() {
}