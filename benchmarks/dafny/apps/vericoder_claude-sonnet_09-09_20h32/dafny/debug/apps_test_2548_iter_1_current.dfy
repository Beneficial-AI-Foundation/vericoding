predicate ValidInput(digits: seq<int>)
{
    |digits| >= 1 && forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
}

predicate IsGoodSubarray(digits: seq<int>, start: int, end: int)
    requires 0 <= start <= end < |digits|
{
    var subarray_sum := Sum(digits[start..end+1]);
    var subarray_length := end - start + 1;
    subarray_sum == subarray_length
}

function Sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

function CountGoodSubarrays(digits: seq<int>): int
    requires ValidInput(digits)
{
    CountGoodSubarraysHelper(digits, 0, map[0 := 1], 0, 0)
}

function CountGoodSubarraysHelper(digits: seq<int>, pos: int, freq_map: map<int, int>, 
                                current_sum: int, current_count: int): int
    requires 0 <= pos <= |digits|
    requires ValidInput(digits)
    requires current_count == pos
    requires current_sum >= 0
    requires forall k :: k in freq_map ==> freq_map[k] >= 0
    requires 0 in freq_map ==> freq_map[0] >= 1
    ensures CountGoodSubarraysHelper(digits, pos, freq_map, current_sum, current_count) >= 0
    decreases |digits| - pos
{
    if pos >= |digits| then 0
    else
        var new_sum := current_sum + digits[pos];
        var new_count := current_count + 1;
        var diff := new_count - new_sum;
        var contribution := if diff in freq_map then freq_map[diff] else 0;
        var new_freq_map := freq_map[diff := if diff in freq_map then freq_map[diff] + 1 else 1];
        contribution + CountGoodSubarraysHelper(digits, pos + 1, new_freq_map, new_sum, new_count)
}

// <vc-helpers>
lemma FreqMapNonNegative(freq_map: map<int, int>, key: int, value: int)
    requires forall k :: k in freq_map ==> freq_map[k] >= 0
    requires value >= 0
    ensures forall k :: k in freq_map[key := value] ==> freq_map[key := value][k] >= 0
{
}

lemma FreqMapContainsZero(freq_map: map<int, int>, key: int, value: int)
    requires 0 in freq_map ==> freq_map[0] >= 1
    requires value >= 0
    ensures 0 in freq_map[key := value] ==> freq_map[key := value][0] >= 1
{
    if key == 0 && value >= 1 {
        assert freq_map[key := value][0] == value >= 1;
    } else if key != 0 && 0 in freq_map {
        assert freq_map[key := value][0] == freq_map[0] >= 1;
    }
}
// </vc-helpers>

// <vc-spec>
method CountGoodSubarraysInArray(digits: seq<int>) returns (count: int)
    requires ValidInput(digits)
    ensures count >= 0
    ensures count == CountGoodSubarrays(digits)
// </vc-spec>
// <vc-code>
{
    var pos := 0;
    var freq_map := map[0 := 1];
    var current_sum := 0;
    var current_count := 0;
    count := 0;
    
    while pos < |digits|
        invariant 0 <= pos <= |digits|
        invariant current_count == pos
        invariant current_sum >= 0
        invariant forall k :: k in freq_map ==> freq_map[k] >= 0
        invariant 0 in freq_map ==> freq_map[0] >= 1
        invariant count + CountGoodSubarraysHelper(digits, pos, freq_map, current_sum, current_count) == CountGoodSubarrays(digits)
        decreases |digits| - pos
    {
        var new_sum := current_sum + digits[pos];
        var new_count := current_count + 1;
        var diff := new_count - new_sum;
        var contribution := if diff in freq_map then freq_map[diff] else 0;
        var new_freq_map := freq_map[diff := if diff in freq_map then freq_map[diff] + 1 else 1];
        
        FreqMapNonNegative(freq_map, diff, if diff in freq_map then freq_map[diff] + 1 else 1);
        FreqMapContainsZero(freq_map, diff, if diff in freq_map then freq_map[diff] + 1 else 1);
        
        count := count + contribution;
        pos := pos + 1;
        freq_map := new_freq_map;
        current_sum := new_sum;
        current_count := new_count;
    }
}
// </vc-code>

