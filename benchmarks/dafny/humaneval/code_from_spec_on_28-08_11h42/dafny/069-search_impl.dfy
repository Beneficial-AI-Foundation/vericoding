// <vc-helpers>
lemma SetCardinalityHelper(s: seq<int>, x: int, i: int)
    requires 0 <= i < |s|
    ensures |(set j | 0 <= j < i+1 && s[j] == x)| == 
            |(set j | 0 <= j < i && s[j] == x)| + (if s[i] == x then 1 else 0)
{
    var setOld := set j | 0 <= j < i && s[j] == x;
    var setNew := set j | 0 <= j < i+1 && s[j] == x;
    
    if s[i] == x {
        assert setNew == setOld + {i};
        assert i !in setOld;
    } else {
        assert setNew == setOld;
    }
}
// </vc-helpers>

// <vc-spec>
method freq(s: seq<int>, x: int) returns (count: int)
    // post-conditions-start
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == |(set j | 0 <= j < i && s[j] == x)|
  {
    SetCardinalityHelper(s, x, i);
    if s[i] == x {
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
