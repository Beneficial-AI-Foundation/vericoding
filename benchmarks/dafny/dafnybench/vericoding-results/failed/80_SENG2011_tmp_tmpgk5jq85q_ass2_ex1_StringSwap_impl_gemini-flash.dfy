// method verifies

// <vc-helpers>
lemma lemma_multiset_swap<T>(s: seq<T>, i: nat, j: nat)
  requires i < |s| && j < |s|
  ensures multiset(s) == multiset(s[0..i] + s[j..j+1] + s[i+1..j] + s[i..i+1] + s[j+1..])
{
  var s_prime := s[0..i] + s[j..j+1] + s[i+1..j] + s[i..i+1] + s[j+1..];
  calc {
    multiset(s_prime);
    multiset(s[0..i]) + multiset(s[j..j+1]) + multiset(s[i+1..j]) + multiset(s[i..i+1]) + multiset(s[j+1..]);
    multiset(s[0..i]) + multiset({s[j]}) + multiset(s[i+1..j]) + multiset({s[i]}) + multiset(s[j+1..]);
    multiset(s[0..i]) + multiset({s[i]}) + multiset(s[i+1..j]) + multiset({s[j]}) + multiset(s[j+1..]);
    multiset(s);
  }
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
        return s;
    }

    var a := s; 

    if i == j {
        return s;
    }

    var actual_i := i;
    var actual_j := j;

    if actual_i > actual_j {
        var temp_i := actual_i;
        actual_i := actual_j;
        actual_j := temp_i;
    }
    
    // Now we have actual_i < actual_j
    a := s[0..actual_i] + s[actual_j..actual_j+1] + s[actual_i+1..actual_j] + s[actual_i..actual_i+1] + s[actual_j+1..];
    
    lemma_multiset_swap(s, i, j); // This lemma helps prove the multiset preservation.
    return a;
}
// </vc-code>

// string == seq<Char>
//give se2011 ass2 ex1.dfy