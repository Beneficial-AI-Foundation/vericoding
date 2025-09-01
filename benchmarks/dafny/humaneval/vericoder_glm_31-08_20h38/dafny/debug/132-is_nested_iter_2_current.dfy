

// <vc-helpers>
// </vc-helpers>
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
    {
        if s[i] == 0 {
            if firstZeroIndex == -1 {
                firstZeroIndex := i;
            } else if secondZeroIndex == -1 {
                secondZeroIndex := i;
                onesAfterSecondZero := 0;  // Reset counter when finding second zero
            }
        } else if s[i] == 1 && secondZeroIndex != -1 {
            onesAfterSecondZero := onesAfterSecondZero + 1;
            if onesAfterSecondZero == 2 {
                return true;
            }
        }
    }

    return false;
}
// </vc-code>

