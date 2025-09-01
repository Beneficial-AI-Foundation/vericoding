

// <vc-helpers>
ghost predicate TwoZerosAndOnes(s: seq<int>, x: int, y: int, z: int, w: int) {
    0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
}

ghost function CountOnesInRangeExclusive(s: seq<int>, low: int, high: int): int
    requires 0 <= low <= high <= |s|
    reads s
{
    if low == high then 0
    else
        var r := CountOnesInRangeExclusive(s, low, high-1);
        if s[high-1] == 1 then r+1 else r
}
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 
    // post-conditions-start
    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var firstZeroIndex := -1;
    var secondZeroIndex := -1;
    var onesAfterSecondZero := 0;

    for i := 0 to |s|
        invariant firstZeroIndex == -1 ==> secondZeroIndex == -1
        invariant firstZeroIndex != -1 ==> 0 <= firstZeroIndex < i
        invariant secondZeroIndex != -1 ==> firstZeroIndex < secondZeroIndex < i
        invariant onesAfterSecondZero >= 0
        invariant secondZeroIndex != -1 ==> 
            onesAfterSecondZero == CountOnesInRangeExclusive(s, secondZeroIndex+1, i)
        invariant onesAfterSecondZero >= 2 ==> exists x, y, z, w :: 0 <= x < y < z < w < i && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    {
        if i < |s| && s[i] == 0 {
            if firstZeroIndex == -1 {
                firstZeroIndex := i;
            } else if secondZeroIndex == -1 {
                secondZeroIndex := i;
                onesAfterSecondZero := 0;
            }
        } else if i < |s| && s[i] == 1 && secondZeroIndex != -1 {
            onesAfterSecondZero := onesAfterSecondZero + 1;
            if onesAfterSecondZero == 2 {
                return true;
            }
        }
    }

    return false;
}
// </vc-code>

