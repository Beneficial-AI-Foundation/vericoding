predicate ValidInput(n: int, numbers: seq<int>)
{
    n >= 3 && n % 3 == 0 &&
    |numbers| == n &&
    forall i :: 0 <= i < |numbers| ==> 1 <= numbers[i] <= 7
}

predicate ValidTriplet(triplet: seq<int>)
{
    |triplet| == 3 &&
    triplet[0] < triplet[1] < triplet[2] &&
    triplet[0] > 0 && triplet[1] > 0 && triplet[2] > 0 &&
    triplet[1] % triplet[0] == 0 && triplet[2] % triplet[1] == 0
}

function FlattenPartition(result: seq<seq<int>>): seq<int>
{
    if |result| == 0 then [] else
    result[0] + FlattenPartition(result[1..])
}

predicate ValidPartition(result: seq<seq<int>>, numbers: seq<int>)
{
    |result| == |numbers| / 3 &&
    (forall i :: 0 <= i < |result| ==> ValidTriplet(result[i])) &&
    multiset(numbers) == multiset(FlattenPartition(result))
}

predicate NoPartitionExists(result: seq<seq<int>>)
{
    |result| == 0
}

// <vc-helpers>
function FindValidPartition(numbers: seq<int>) : (result: seq<seq<int>>)
{
  if |numbers| < 3 then []
  else if |numbers| % 3 != 0 then []  // Should not happen given ValidInput constraints
  else
    var sorted_numbers := Sort(numbers);
    var i := 0;
    while i <= |sorted_numbers| - 3
      invariant 0 <= i <= |sorted_numbers| - 1
      invariant Sorted(sorted_numbers)
    {
      var a := sorted_numbers[i];
      var j := i + 1;
      while j <= |sorted_numbers| - 2
        invariant i + 1 <= j <= |sorted_numbers| - 1
        invariant Sorted(sorted_numbers)
      {
        var b := sorted_numbers[j];
        if b % a == 0
        {
          var k := j + 1;
          while k <= |sorted_numbers| - 1
            invariant j + 1 <= k <= |sorted_numbers| - 1
            invariant Sorted(sorted_numbers)
          {
            var c := sorted_numbers[k];
            if c % b == 0 && a < b && b < c
            {
              var triplet := [a, b, c];
              if ValidTriplet(triplet)
              {
                var remaining_numbers_multiset := multiset(sorted_numbers) - multiset(triplet);
                var remaining_numbers_seq := MultisetToSeq(remaining_numbers_multiset);
                var sub_result := FindValidPartition(remaining_numbers_seq);

                if sub_result != [] || remaining_numbers_multiset == multiset([]) // If sub_result is not empty OR remaining numbers are empty
                {
                  return [triplet] + sub_result;
                }
              }
            }
            k := k + 1;
          }
        }
        j := j + 1;
      }
      i := i + 1;
    }
    [];
}

function Sort(s: seq<int>): seq<int>
  ensures sorted(s)
  ensures multiset(s) == old(multiset(s))
{
  if |s| <= 1 then s
  else
    var pivot := s[0];
    var less: seq<int> := [];
    var greater: seq<int> := [];
    for i := 1 to |s|-1
    {
      if s[i] <= pivot then less := less + [s[i]];
      else greater := greater + [s[i]];
    }
    Sort(less) + [pivot] + Sort(greater)
}

predicate sorted(s: seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

// Function to convert a multiset to a sequence, maintains order if possible from original
// This is non-deterministic in general, but for our purpose, any valid sequence is fine.
// We need this helper to allow recursive calls to FindValidPartition with sequences.
function MultisetToSeq(m: multiset<int>): seq<int>
  ensures multiset(MultisetToSeq(m)) == m
{
  if m.empty then []
  else
    var k: int := m.Keys.Any();
    var count: nat := m[k];
    seq_of(k, count) + MultisetToSeq(m - multiset{k := count})
}

function seq_of(val: int, count: nat): seq<int>
  ensures |seq_of(val, count)| == count
  ensures forall i :: 0 <= i < count ==> seq_of(val, count)[i] == val
{
  if count == 0 then []
  else [val] + seq_of(val, count - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, numbers: seq<int>) returns (result: seq<seq<int>>)
    requires ValidInput(n, numbers)
    ensures NoPartitionExists(result) || ValidPartition(result, numbers)
// </vc-spec>
// <vc-code>
{
  var sorted_numbers := Sort(numbers);
  var result_option := FindValidPartition(sorted_numbers);

  // If result_option is not empty, check if it's a valid partition.
  // We need to ensure that the multiset of the original `numbers` matches
  // the flattened multiset of `result_option`.
  if result_option != [] && ValidPartition(result_option, numbers) then
    return result_option;
  else
    return []; // No valid partition found among many options or if the one found is not perfect.
}
// </vc-code>

