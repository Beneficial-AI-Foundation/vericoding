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
lemma MapKeysPresenceAndUpdate<U>(m: map<int,U>, key: int, value: U)
  ensures key in m[key := value]
  ensures m[key := value][key] == value
{
}

lemma MapKeysOtherPresence<U>(m: map<int,U>, key1: int, key2: int, value: U)
  requires key1 != key2
  ensures key2 in m ==> key2 in m[key1 := value]
  ensures key2 in m ==> m[key1 := value][key2] == m[key2]
{
}

lemma MapKeysOtherAbsence<U>(m: map<int,U>, key1: int, key2: int, value: U)
  requires key1 != key2
  requires key2 !in m
  ensures key2 !in m[key1 := value]
{
}

lemma MapPositiveValuesUpdate(m: map<int,int>, key: int, value: int)
  requires forall k :: k in m ==> m[k] >= 0
  requires value >= 0
  ensures forall k :: k in m[key := value] ==> m[key := value][k] >= 0
{
  forall k | k in m[key := value]
    ensures m[key := value][k] >= 0
  {
    if k == key {
      assert m[key := value][k] == value;
    } else {
      assert m[key := value][k] == m[k];
    }
  }
}

lemma MapUpdatePreservesPositiveValues(m: map<int,int>, key: int, value: int, k: int)
  requires forall k' :: k' in m ==> m[k'] >= 0
  requires value >= 0
  requires k in m[key := value]
  ensures m[key := value][k] >= 0
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountGoodSubarraysInArray(digits: seq<int>) returns (count: int)
    requires ValidInput(digits)
    ensures count >= 0
    ensures count == CountGoodSubarrays(digits)
// </vc-spec>
// <vc-code>
{
  count := 0;
  var pos := 0;
  var current_sum := 0;
  var current_count := 0;
  var freq_map : map<int, int> := map[0 := 1];
  
  while pos < |digits|
    invariant 0 <= pos <= |digits|
    invariant current_count == pos
    invariant current_sum >= 0
    invariant forall k :: k in freq_map ==> freq_map[k] >= 0
    invariant 0 in freq_map && freq_map[0] >= 1
    invariant count >= 0
    invariant count + CountGoodSubarraysHelper(digits, pos, freq_map, current_sum, current_count)
            == CountGoodSubarrays(digits)
  {
    var new_sum := current_sum + digits[pos];
    var new_count := current_count + 1;
    var diff := new_count - new_sum;
    
    var contribution := 0;
    if diff in freq_map {
      contribution := freq_map[diff];
    }
    count := count + contribution;
    
    var new_val := if diff in freq_map then freq_map[diff] + 1 else 1;
    freq_map := freq_map[diff := new_val];
    
    current_sum := new_sum;
    current_count := new_count;
    pos := pos + 1;
  }
}
// </vc-code>

