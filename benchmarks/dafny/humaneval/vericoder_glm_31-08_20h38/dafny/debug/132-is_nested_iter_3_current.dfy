

// <vc-helpers>
ghost predicate TwoZerosAndOnes(s: seq<int>, x: int, y: int, z: int, w: int) {
    0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
}

lemma lemma_ones_after_second_zero(s: seq<int>, secondZero: int, count: int, i: int)
    requires secondZero != -1
    requires 0 <= secondZero < i <= |s|
    requires forall k :: secondZero < k < i ==> s[k] == 1 ==>
        count == (if k > secondZero then 1 else 0) + (if k > secondZero + 1 then 1 else 0)
    ensures forall z, w :: secondZero < z < w < |s| && s[z] == 1 && s[w] == 1 ==> 
        count >= 2 ==> exists x, y :: 0 <= x < y <= secondZero && s[x] == 0 && s[y] == 0
{
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
            onesAfterSecondZero == (if i > secondZeroIndex then (var count := 0; 
                for j := secondZeroIndex + 1 to i
                    invariant count == j - (secondZeroIndex + 1)
                    invariant forall k :: secondZeroIndex < k < j ==> s[k] == 1
                {
                    if s[j] == 1 { count := count + 1; }
                } 
                count) else 0)
        invariant onesAfterSecondZero >= 2 ==> exists x, y, z, w :: 0 <= x < y < z < w < i && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    {
        if s[i] == 0 {
            if firstZeroIndex == -1 {
                firstZeroIndex := i;
            } else if secondZeroIndex == -1 {
                secondZeroIndex := i;
                onesAfterSecondZero := 0;
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

