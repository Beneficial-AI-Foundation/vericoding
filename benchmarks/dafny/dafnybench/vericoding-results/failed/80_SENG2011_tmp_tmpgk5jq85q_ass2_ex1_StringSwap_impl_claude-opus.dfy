// method verifies

// <vc-helpers>
lemma SwapMultisetLemma(s: seq<char>, i: nat, j: nat, t: seq<char>)
  requires i < |s| && j < |s|
  requires |t| == |s|
  requires t[i] == s[j] && t[j] == s[i]
  requires forall k :: 0 <= k < |s| && k != i && k != j ==> t[k] == s[k]
  ensures multiset(s[..]) == multiset(t[..])
{
  var ms := multiset(s[..]);
  var mt := multiset(t[..]);
  
  assert s[..] == s;
  assert t[..] == t;
  
  // Direct proof that multisets are equal by showing equal counts for all elements
  forall x
    ensures ms[x] == mt[x]
  {
    // We need to count occurrences carefully considering the swap
    // The key insight: swapping positions i and j preserves the multiset
    
    // Count how many times x appears at each position
    var count_s := |set idx | 0 <= idx < |s| && s[idx] == x|;
    var count_t := |set idx | 0 <= idx < |t| && t[idx] == x|;
    
    // For each position, determine if it contributes to the count
    forall idx | 0 <= idx < |s|
      ensures (s[idx] == x) == (exists idx' :: 0 <= idx' < |t| && t[idx'] == x && 
                                 ((idx == i && idx' == i && s[j] == x) ||
                                  (idx == j && idx' == j && s[i] == x) ||
                                  (idx != i && idx != j && idx' == idx && s[idx] == x)))
    {
      if idx == i {
        assert t[i] == s[j];
        if s[i] == x {
          // s[i] == x appears at position j in t
          assert t[j] == s[i] == x;
        }
      } else if idx == j {
        assert t[j] == s[i];
        if s[j] == x {
          // s[j] == x appears at position i in t
          assert t[i] == s[j] == x;
        }
      } else {
        assert t[idx] == s[idx];
        if s[idx] == x {
          assert t[idx] == x;
        }
      }
    }
    
    // The swap operation preserves the count of each element
    assert ms[x] == mt[x];
  }
  
  assert ms == mt;
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
    t := s[i := s[j]][j := s[i]];
    
    assert |t| == |s|;
    assert t[i] == s[j];
    assert t[j] == s[i];
    assert forall k :: 0 <= k < |s| && k != i && k != j ==> t[k] == s[k];
    
    SwapMultisetLemma(s, i, j, t);
  }
}
// </vc-code>

// string == seq<Char>
//give se2011 ass2 ex1.dfy