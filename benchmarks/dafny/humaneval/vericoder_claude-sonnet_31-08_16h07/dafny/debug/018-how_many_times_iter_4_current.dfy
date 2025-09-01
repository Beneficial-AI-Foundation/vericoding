

// <vc-helpers>
lemma EmptySubstrCardinality(s: string, substr: string)
    requires |substr| == 0 || |substr| > |s|
    ensures |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr| == 0
{
    if |substr| == 0 {
        var validSet := set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr;
        forall i | i in validSet 
        ensures false
        {
            assert 0 <= i <= |s| - |substr|;
            assert s[i..i+|substr|] == substr;
            assert s[i..i+0] == "";
            assert s[i..i] == "";
            assert "" == substr;
        }
        assert validSet == {};
        assert |validSet| == 0;
    } else {
        assert |substr| > |s|;
        assert |s| - |substr| < 0;
        var validSet := set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr;
        forall i | i in validSet 
        ensures false
        {
            assert 0 <= i <= |s| - |substr|;
            assert 0 <= i;
            assert i <= |s| - |substr|;
            assert |s| - |substr| < 0;
            assert i < 0;
        }
        assert validSet == {};
        assert |validSet| == 0;
    }
}

lemma SetInvariantMaintained(s: string, substr: string, i: int, times: int)
    requires 0 <= i <= |s| - |substr|
    requires times == |set j {:trigger s[j..j+|substr|]} | 0 <= j < i && s[j..j+|substr|] == substr|
    ensures if s[i..i+|substr|] == substr 
            then times + 1 == |set j {:trigger s[j..j+|substr|]} | 0 <= j < i + 1 && s[j..j+|substr|] == substr|
            else times == |set j {:trigger s[j..j+|substr|]} | 0 <= j < i + 1 && s[j..j+|substr|] == substr|
{
    var oldSet := set j {:trigger s[j..j+|substr|]} | 0 <= j < i && s[j..j+|substr|] == substr;
    var newSet := set j {:trigger s[j..j+|substr|]} | 0 <= j < i + 1 && s[j..j+|substr|] == substr;
    
    if s[i..i+|substr|] == substr {
        assert newSet == oldSet + {i};
        assert i !in oldSet;
        assert |newSet| == |oldSet| + 1;
    } else {
        assert newSet == oldSet;
        assert |newSet| == |oldSet|;
    }
}

lemma FinalEquivalence(s: string, substr: string, times: int)
    requires |substr| > 0 && |substr| <= |s|
    requires times == |set j {:trigger s[j..j+|substr|]} | 0 <= j < |s| - |substr| + 1 && s[j..j+|substr|] == substr|
    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
{
    var setA := set j {:trigger s[j..j+|substr|]} | 0 <= j < |s| - |substr| + 1 && s[j..j+|substr|] == substr;
    var setB := set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr;
    
    assert setA == setB;
}
// </vc-helpers>

// <vc-spec>
method how_many_times(s: string, substr: string) returns (times: int)
    // post-condition-start
    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
    // post-condition-end
// </vc-spec>
// <vc-code>
{
  times := 0;
  if |substr| == 0 || |substr| > |s| {
    EmptySubstrCardinality(s, substr);
    return;
  }
  
  var i := 0;
  while i <= |s| - |substr|
    invariant 0 <= i <= |s| - |substr| + 1
    invariant times == |set j {:trigger s[j..j+|substr|]} | 0 <= j < i && s[j..j+|substr|] == substr|
  {
    SetInvariantMaintained(s, substr, i, times);
    if s[i..i+|substr|] == substr {
      times := times + 1;
    }
    i := i + 1;
  }
  
  FinalEquivalence(s, substr, times);
}
// </vc-code>

