// <vc-preamble>
function MinSpec(s: seq<int>): int
    requires 0 < |s|
    decreases |s|
{
    if |s| == 1 then
        s[0]
    else if |s| == 0 then
        0
    else
        var laterMin := MinSpec(s[1..]);
        if s[0] <= laterMin then
            s[0]
        else
            laterMin
}
// </vc-preamble>

// <vc-helpers>
lemma MinSpecProperty(s: seq<int>, i: int)
    requires 0 < |s|
    requires 0 <= i < |s|
    ensures MinSpec(s) <= s[i]
    decreases |s|
{
    if |s| == 1 {
        assert s[0] == s[i];
    } else {
        if i == 0 {
            var laterMin := MinSpec(s[1..]);
            if s[0] <= laterMin {
                assert MinSpec(s) == s[0];
            } else {
                assert MinSpec(s) == laterMin;
                MinSpecProperty(s[1..], 0);
            }
        } else {
            MinSpecProperty(s[1..], i-1);
            assert s[1..][i-1] == s[i];
        }
    }
}

lemma MinSpecIsMin(s: seq<int>)
    requires 0 < |s|
    ensures exists j :: 0 <= j < |s| && s[j] == MinSpec(s)
    decreases |s|
{
    if |s| == 1 {
        assert s[0] == MinSpec(s);
    } else {
        var laterMin := MinSpec(s[1..]);
        if s[0] <= laterMin {
            assert s[0] == MinSpec(s);
        } else {
            MinSpecIsMin(s[1..]);
            var j :| 0 <= j < |s[1..]| && s[1..][j] == MinSpec(s[1..]);
            assert s[j+1] == MinSpec(s);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method SecondSmallest(numbers: array<int>) returns (indices: (int, int))
    requires numbers.Length >= 2
    ensures 0 <= indices.0 < numbers.Length && 0 <= indices.1 < numbers.Length
    ensures forall k :: 0 <= k < numbers.Length && k != indices.0 && numbers[indices.0] == MinSpec(numbers[..]) ==> numbers[k] >= numbers[indices.1]
    ensures exists k :: 0 <= k < numbers.Length && k != indices.0 && numbers[k] == numbers[indices.1]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed min value finding logic */
    var minIdx := 0;
    var minVal := numbers[0];
    var secondIdx := if numbers.Length > 1 && numbers[1] < numbers[0] then 0 else 1;
    var secondVal := if numbers.Length > 1 && numbers[1] < numbers[0] then numbers[0] else numbers[1];
    
    if numbers.Length > 1 && numbers[1] < numbers[0] {
        minIdx := 1;
        minVal := numbers[1];
    }
    
    var i := 2;
    while i < numbers.Length
        invariant 2 <= i <= numbers.Length
        invariant 0 <= minIdx < numbers.Length
        invariant 0 <= secondIdx < numbers.Length
        invariant minVal == numbers[minIdx]
        invariant secondVal == numbers[secondIdx]
        invariant forall k :: 0 <= k < i ==> minVal <= numbers[k]
        invariant minIdx < i && secondIdx < i
        invariant exists k :: 0 <= k < i && k != minIdx && numbers[k] == secondVal
        invariant forall k :: 0 <= k < i && k != minIdx ==> secondVal <= numbers[k]
    {
        if numbers[i] < minVal {
            secondIdx := minIdx;
            secondVal := minVal;
            minIdx := i;
            minVal := numbers[i];
        } else if numbers[i] < secondVal {
            secondIdx := i;
            secondVal := numbers[i];
        }
        i := i + 1;
    }
    
    var k := 0;
    while k < numbers.Length
        invariant 0 <= k <= numbers.Length
        invariant forall m :: 0 <= m < k ==> MinSpec(numbers[..]) <= numbers[m]
    {
        MinSpecProperty(numbers[..], k);
        k := k + 1;
    }
    
    MinSpecIsMin(numbers[..]);
    var j :| 0 <= j < numbers.Length && numbers[j] == MinSpec(numbers[..]);
    
    assert forall m :: 0 <= m < numbers.Length ==> minVal <= numbers[m];
    assert minVal == numbers[minIdx];
    assert numbers[j] == MinSpec(numbers[..]);
    assert forall m :: 0 <= m < numbers.Length ==> MinSpec(numbers[..]) <= numbers[m];
    assert MinSpec(numbers[..]) <= numbers[j];
    assert numbers[j] <= numbers[j];
    assert minVal == MinSpec(numbers[..]);
    
    indices := (minIdx, secondIdx);
}
// </vc-code>
