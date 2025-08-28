// <vc-helpers>
lemma SetsEqual(s: string, substr: string, i: int)
    requires |substr| > 0
    requires i == |s| - |substr| + 1
    ensures (set j {:trigger s[j..j+|substr|]} | 0 <= j < i && s[j..j+|substr|] == substr) == (set j {:trigger s[j..j+|substr|]} | 0 <= j <= |s| - |substr| && s[j..j+|substr|] == substr)
{
    var set1 := set j {:trigger s[j..j+|substr|]} | 0 <= j < i && s[j..j+|substr|] == substr;
    var set2 := set j {:trigger s[j..j+|substr|]} | 0 <= j <= |s| - |substr| && s[j..j+|substr|] == substr;
    assert set1 == set2;
}

lemma EmptySubstrSet(s: string, substr: string)
    requires |substr| == 0
    ensures (set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr) == (set i | 0 <= i <= |s|)
{
}

lemma EmptySubstrSize(s: string)
    ensures |set i | 0 <= i <= |s|| == |s| + 1
{
}

lemma SetUpdate(s: string, substr: string, i: int)
    requires |substr| > 0
    requires 0 <= i <= |s| - |substr|
    ensures |set j {:trigger s[j..j+|substr|]} | 0 <= j < i + 1 && s[j..j+|substr|] == substr| == 
            |set j {:trigger s[j..j+|substr|]} | 0 <= j < i && s[j..j+|substr|] == substr| + 
            (if s[i..i+|substr|] == substr then 1 else 0)
{
    var oldSet := set j {:trigger s[j..j+|substr|]} | 0 <= j < i && s[j..j+|substr|] == substr;
    var newSet := set j {:trigger s[j..j+|substr|]} | 0 <= j < i + 1 && s[j..j+|substr|] == substr;
    
    if s[i..i+|substr|] == substr {
        assert i in newSet;
        assert i !in oldSet;
        assert newSet == oldSet + {i};
    } else {
        assert newSet == oldSet;
    }
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
  if |substr| == 0 {
    EmptySubstrSet(s, substr);
    EmptySubstrSize(s);
    return |s| + 1;
  }
  
  if |substr| > |s| {
    assert (set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr) == {};
    return 0;
  }
  
  times := 0;
  var i := 0;
  
  while i <= |s| - |substr|
    invariant 0 <= i <= |s| - |substr| + 1
    invariant times == |set j {:trigger s[j..j+|substr|]} | 0 <= j < i && s[j..j+|substr|] == substr|
  {
    if s[i..i+|substr|] == substr {
      times := times + 1;
    }
    SetUpdate(s, substr, i);
    i := i + 1;
  }
  
  assert times == |set j {:trigger s[j..j+|substr|]} | 0 <= j < i && s[j..j+|substr|] == substr|;
  assert i == |s| - |substr| + 1;
  SetsEqual(s, substr, i);
}
// </vc-code>
