// method verifies

// <vc-helpers>
lemma MultisetSwapPreservation(s: string, i: nat, j: nat, t: string)
requires i < |s| && j < |s|
requires |s| == |t|
requires forall k: nat :: k < |s| && k != i && k != j ==> t[k] == s[k]
requires t[i] == s[j] && t[j] == s[i]
ensures multiset(s[..]) == multiset(t[..])
{
    if |s| <= 1 {
        return;
    }
    
    var ms := multiset(s[..]);
    var mt := multiset(t[..]);
    
    assert s[..] == s;
    assert t[..] == t;
    
    if i == j {
        assert t == s;
        return;
    }
    
    // When characters are the same
    if s[i] == s[j] {
        // All characters at positions other than i,j remain the same
        forall c | c !in {s[i]} 
        ensures ms[c] == mt[c]
        {
            var s_count := |set k | 0 <= k < |s| && s[k] == c|;
            var t_count := |set k | 0 <= k < |t| && t[k] == c|;
            assert s_count == t_count;
        }
        // Character at positions i and j stays the same count
        var same_char := s[i];
        var s_same_count := |set k | 0 <= k < |s| && s[k] == same_char|;
        var t_same_count := |set k | 0 <= k < |t| && t[k] == same_char|;
        assert s_same_count == t_same_count;
        assert mt[same_char] == ms[same_char];
    } else {
        // When characters are different
        // Characters other than s[i] and s[j] have same counts
        forall c | c !in {s[i], s[j]}
        ensures ms[c] == mt[c]
        {
            var s_positions := set k | 0 <= k < |s| && s[k] == c;
            var t_positions := set k | 0 <= k < |t| && t[k] == c;
            assert s_positions == t_positions;
        }
        
        // s[i] appears where s[j] was, plus all other original positions
        var s_i_char := s[i];
        var s_j_char := s[j];
        
        var s_i_positions := set k | 0 <= k < |s| && s[k] == s_i_char;
        var t_i_positions := set k | 0 <= k < |t| && t[k] == s_i_char;
        var s_j_positions := set k | 0 <= k < |s| && s[k] == s_j_char;
        var t_j_positions := set k | 0 <= k < |t| && t[k] == s_j_char;
        
        // After swap: s[i] appears at j and all its original positions except i
        // s[j] appears at i and all its original positions except j
        assert t_i_positions == (s_i_positions - {i}) + {j};
        assert t_j_positions == (s_j_positions - {j}) + {i};
        assert |t_i_positions| == |s_i_positions|;
        assert |t_j_positions| == |s_j_positions|;
        assert mt[s_i_char] == ms[s_i_char];
        assert mt[s_j_char] == ms[s_j_char];
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
    
    var result := s;
    var temp := s[i];
    result := result[i := s[j]];
    result := result[j := temp];
    
    assert |s| == |result|;
    assert forall k: nat :: k < |s| && k != i && k != j ==> result[k] == s[k];
    assert result[i] == s[j] && result[j] == s[i];
    
    MultisetSwapPreservation(s, i, j, result);
    
    return result;
}
// </vc-code>

// string == seq<Char>
//give se2011 ass2 ex1.dfy