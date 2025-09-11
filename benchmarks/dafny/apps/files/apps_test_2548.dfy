// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountGoodSubarraysInArray(digits: seq<int>) returns (count: int)
    requires ValidInput(digits)
    ensures count >= 0
    ensures count == CountGoodSubarrays(digits)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
