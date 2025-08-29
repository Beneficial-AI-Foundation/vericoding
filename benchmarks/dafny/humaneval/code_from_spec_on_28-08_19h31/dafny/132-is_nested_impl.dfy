// <vc-helpers>
// No additional helpers needed for this verification.
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 
    // post-conditions-start
    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
method IsNested(s: seq<int>) returns (res: bool)
    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
{
    var n := |s|;
    if n < 4 {
        return false;
    }
    
    var foundFirstZero := false;
    var foundSecondZero := false;
    var foundFirstOne := false;
    var foundSecondOne := false;
    
    var firstZeroIdx := -1;
    var secondZeroIdx := -1;
    var firstOneIdx := -1;
    var secondOneIdx := -1;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant foundFirstZero ==> 0 <= firstZeroIdx < i && s[firstZeroIdx] == 0
        invariant foundSecondZero ==> 0 <= firstZeroIdx < i && 0 <= secondZeroIdx < i && firstZeroIdx < secondZeroIdx && s[firstZeroIdx] == 0 && s[secondZeroIdx] == 0
        invariant foundFirstOne ==> 0 <= firstZeroIdx < i && 0 <= secondZeroIdx < i && 0 <= firstOneIdx < i && firstZeroIdx < secondZeroIdx && secondZeroIdx < firstOneIdx && s[firstZeroIdx] == 0 && s[secondZeroIdx] == 0 && s[firstOneIdx] == 1
        invariant foundSecondOne ==> 0 <= firstZeroIdx < i && 0 <= secondZeroIdx < i && 0 <= firstOneIdx < i && 0 <= secondOneIdx < i && firstZeroIdx < secondZeroIdx && secondZeroIdx < firstOneIdx && firstOneIdx < secondOneIdx && s[firstZeroIdx] == 0 && s[secondZeroIdx] == 0 && s[firstOneIdx] == 1 && s[secondOneIdx] == 1
    {
        if !foundFirstZero && s[i] == 0 {
            foundFirstZero := true;
            firstZeroIdx := i;
        } else if foundFirstZero && !foundSecondZero && s[i] == 0 {
            foundSecondZero := true;
            secondZeroIdx := i;
        } else if foundSecondZero && !foundFirstOne && s[i] == 1 {
            foundFirstOne := true;
            firstOneIdx := i;
        } else if foundFirstOne && !foundSecondOne && s[i] == 1 {
            foundSecondOne := true;
            secondOneIdx := i;
        }
        i := i + 1;
    }
    
    res := foundSecondOne;
    if res {
        assert 0 <= firstZeroIdx < secondZeroIdx < firstOneIdx < secondOneIdx < n;
        assert s[firstZeroIdx] == 0 && s[secondZeroIdx] == 0 && s[firstOneIdx] == 1 && s[secondOneIdx] == 1;
    }
}
// </vc-code>
