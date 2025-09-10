predicate ValidInput(n: int, aa: seq<int>)
{
    n >= 2 &&
    |aa| == n - 1 &&
    forall i :: 0 <= i < |aa| ==> 1 <= aa[i] < i + 2
}

function SubordinateCount(aa: seq<int>, boss_id: int): int
{
    |set j | 0 <= j < |aa| && aa[j] == boss_id|
}

predicate ValidOutput(n: int, aa: seq<int>, result: seq<int>)
{
    |result| == n &&
    forall i :: 0 <= i < n ==> result[i] >= 0 &&
    forall i :: 0 <= i < n ==> result[i] == SubordinateCount(aa, i + 1)
}

// <vc-helpers>
function CountOccurrences(s: seq<int>, value: int): int
  decreases |s|
{
  if |s| == 0 then
    0
  else
    (if s[0] == value then 1 else 0) + CountOccurrences(s[1..], value)
}
// This helper lemma proves the equivalence between CountOccurrences function and the set comprehension for counting occurrences.
lemma CountOccurrencesProperties(s: seq<int>, value: int)
  ensures CountOccurrences(s, value) == |set j | 0 <= j < |s| && s[j] == value|
{
  if |s| == 0 {
    // Base case: trivially true
  } else {
    // Inductive step: prove for s[1..] and then extend to s
    CountOccurrencesProperties(s[1..], value);
    if s[0] == value {
      // If the first element matches, it contributes 1 to the count
      calc {
        CountOccurrences(s, value);
        1 + CountOccurrences(s[1..], value); // By definition of CountOccurrences
        {
          // Apply the lemma for the tail of the sequence
          assert CountOccurrences(s[1..], value) == |set j | 0 <= j < |s[1..]| && s[1..][j] == value|;
        }
        1 + |set j | 0 <= j < |s[1..]| && s[1..][j] == value|;
        {
          // The set of indices `j` in `s[1..]` such that `s[1..][j] == value`
          // is equivalent to `1 + |set j | 1 <= j < |s| && s[j] == value|;` if `s[0] == value`
          // or `|set j | 1 <= j < |s| && s[j] == value|;` if `s[0] != value`
          // when `s[0] == value`, we have `s[0]` contributing 1 to count along with subsequent elements
          assert forall k :: 0 <= k < |s[1..]| ==> (s[1..][k] == value) == (s[k+1] == value);
          assert |set j | 0 <= j < |s[1..]| && s[1..][j] == value| == |set j | 1 <= j < |s| && s[j] == value|;
          assert |set j | 0 <= j < |s| && s[j] == value| == 1 + |set j | 1 <= j < |s| && s[j] == value|;
        }
        |set j | 0 <= j < |s| && s[j] == value|;
      }
    } else {
      // If the first element doesn't match, it contributes 0 to the count
      calc {
        CountOccurrences(s, value);
        0 + CountOccurrences(s[1..], value); // By definition of CountOccurrences
        {
          // Apply the lemma for the tail of the sequence
          assert CountOccurrences(s[1..], value) == |set j | 0 <= j < |s[1..]| && s[1..][j] == value|;
        }
        |set j | 0 <= j < |s[1..]| && s[1..][j] == value|;
        {
          // The set of indices `j` in `s[1..]` such that `s[1..][j] == value`
          // is equivalent to `|set j | 1 <= j < |s| && s[j] == value|;`
          // when `s[0] != value`, `s[0]` doesn't contribute and count relies on subsequent elements
          assert forall k :: 0 <= k < |s[1..]| ==> (s[1..][k] == value) == (s[k+1] == value);
          assert |set j | 0 <= j < |s[1..]| && s[1..][j] == value| == |set j | 1 <= j < |s| && s[j] == value|;
          assert |set j | 0 <= j < |s| && s[j] == value| == |set j | 1 <= j < |s| && s[j] == value|;
        }
        |set j | 0 <= j < |s| && s[j] == value|;
      }
    }
  }
}

lemma SubordinateCountMatch(aa: seq<int>, boss_id: int)
    ensures SubordinateCount(aa, boss_id) == CountOccurrences(aa, boss_id)
{
    CountOccurrencesProperties(aa, boss_id);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, aa: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, aa)
    ensures ValidOutput(n, aa, result)
// </vc-spec>
// <vc-code>
{
  var result_arr: array<int> := new int[n];

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> result_arr[k] == SubordinateCount(aa, k + 1)
  {
    var current_boss_id := i + 1;
    // Call the lemma to prove the equivalence needed for the postcondition.
    SubordinateCountMatch(aa, current_boss_id);
    result_arr[i] := CountOccurrences(aa, current_boss_id);
    i := i + 1;
  }

  result := result_arr[..];
}
// </vc-code>

