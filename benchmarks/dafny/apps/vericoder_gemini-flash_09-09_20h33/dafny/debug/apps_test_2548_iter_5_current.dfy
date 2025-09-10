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
// No changes needed in this section as the previous errors were due to duplicate declarations.
// The functions from the preamble should be used instead.
// </vc-helpers>

// <vc-spec>
method CountGoodSubarraysInArray(digits: seq<int>) returns (count: int)
    requires ValidInput(digits)
    ensures count >= 0
    ensures count == CountGoodSubarrays(digits)
// </vc-spec>
// <vc-code>
{
    var current_sum := 0;
    var result_count := 0;
    var freq_map: map<int, int> := map[0 := 1]; // diff (count - sum) -> frequency

    for i := 0 to |digits| - 1
        invariant 0 <= i <= |digits|
        invariant current_sum >= 0
        invariant result_count >= 0
        invariant forall k :: k in freq_map ==> freq_map[k] >= 0
        invariant 0 in freq_map ==> freq_map[0] >= 1
        invariant forall d, k | d in map domain freq_map && k in map domain freq_map :: d < k ==> current_sum + freq_map[d] <= current_sum + freq_map[k] // This invariant helps with the proof of CountGoodSubarrays
        invariant result_count == CountGoodSubarraysHelper(digits, 0, map[0 := 1], 0, 0) - CountGoodSubarraysHelper(digits, i, freq_map, current_sum, i) + CountGoodSubarraysHelper(digits, i+1, freq_map, current_sum, i+1) // More complex invariant may be needed for exact equality
        invariant current_sum == Sum(digits[..i])
        invariant forall k :: k in freq_map ==> k + current_sum >= 0 // The diff (i+1 - current_sum) can be negative if sum is large
        invariant current_sum <= (i+1) * 9 // Sum upper bound
    {
        current_sum := current_sum + digits[i];
        var current_diff := (i + 1) - current_sum;

        if current_diff in freq_map {
            result_count := result_count + freq_map[current_diff];
            freq_map := freq_map[current_diff := freq_map[current_diff] + 1];
        } else {
            freq_map := freq_map[current_diff := 1];
        }
    }
    return result_count;
}
// </vc-code>

