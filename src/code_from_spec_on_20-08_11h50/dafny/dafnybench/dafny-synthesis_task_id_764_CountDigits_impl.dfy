lemma SetSizeIncrement(s: string, j: int)
    requires 0 <= j < |s|
    ensures |set i: int | 0 <= i < j + 1 && IsDigit(s[i])| == 
            |set i: int | 0 <= i < j && IsDigit(s[i])| + (if IsDigit(s[j]) then 1 else 0)
{
    var setJ := set i: int | 0 <= i < j && IsDigit(s[i]);
    var setJ1 := set i: int | 0 <= i < j + 1 && IsDigit(s[i]);
    
    if IsDigit(s[j]) {
        assert setJ1 == setJ + {j};
        assert j !in setJ;
    } else {
        assert setJ1 == setJ;
    }
}

// <vc-spec>
method CountDigits(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsDigit(s[i])|
// </vc-spec>
// <vc-code>
{
  count := 0;
  var j := 0;
  
  while j < |s|
    invariant 0 <= j <= |s|
    invariant count >= 0
    invariant count == | set i: int | 0 <= i < j && IsDigit(s[i])|
  {
    SetSizeIncrement(s, j);
    if IsDigit(s[j]) {
      count := count + 1;
    }
    j := j + 1;
  }
}
// </vc-code>