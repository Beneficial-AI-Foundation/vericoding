// method verifies

// <vc-helpers>
lemma SwapLemma(s: seq<char>, i: nat, j: nat)
  requires i < |s| && j < |s|
  ensures exists t: seq<char> :: 
    |t| == |s| &&
    multiset(s) == multiset(t) &&
    (forall k: nat :: k != i && k != j && k < |s| ==> t[k] == s[k]) &&
    t[i] == s[j] && t[j] == s[i]
{
  var t := s[i := s[j]];
  t := t[j := s[i]];
  assert |t| == |s|;
  assert multiset(s) == multiset(t);
  assert forall k: nat :: k != i && k != j && k < |s| ==> t[k] == s[k];
  assert t[i] == s[j] && t[j] == s[i];
}

function method CharSeqToString(chars: seq<char>): string
{
  if |chars| == 0 then "" 
  else String(chars[0]) + CharSeqToString(chars[1..])
}
// </vc-helpers>

// <vc-spec>
method StringSwap(s: string, i:nat, j:nat) returns (t: string)
requires i >= 0 && j >= 0 && |s| >= 0;
requires |s| > 0 ==> i < |s| && j < |s|;
ensures multiset(s[..]) == multiset(t[..]);
ensures |s| == |t|;
ensures |s| > 0 ==> forall k:nat :: k != i && k != j && k < |s| ==> t[k] == s[k]
ensures |s| > 0 ==> t[i] == s[j] && t[j] == s[i];
ensures |s| == 0 ==> t == s;
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    t := s;
  } else {
    var chars := s[..];
    ghost var t_seq :| 
      |t_seq| == |chars| &&
      multiset(chars) == multiset(t_seq) &&
      (forall k: nat :: k != i && k != j && k < |chars| ==> t_seq[k] == chars[k]) &&
      t_seq[i] == chars[j] && t_seq[j] == chars[i];
    t := CharSeqToString(t_seq);
  }
}
// </vc-code>

// string == seq<Char>
//give se2011 ass2 ex1.dfy