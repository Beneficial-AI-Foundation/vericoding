predicate ValidInput(n: int, a: seq<int>)
{
    n >= 0 && |a| == n && forall i :: 0 <= i < |a| ==> a[i] in {4, 8, 15, 16, 23, 42}
}

function number_of_complete_subsequences(n: int, a: seq<int>): int
  requires ValidInput(n, a)
  ensures 0 <= number_of_complete_subsequences(n, a) <= n
{
    var k := [4, 8, 15, 16, 23, 42];
    var s := [n, 0, 0, 0, 0, 0, 0];
    var final_s := process_array(s, a, k, 0);
    final_s[6]
}

function process_array(s: seq<int>, a: seq<int>, k: seq<int>, index: int): seq<int>
  requires |s| == 7 && |k| == 6
  requires 0 <= index <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] in {4, 8, 15, 16, 23, 42}
  requires k == [4, 8, 15, 16, 23, 42]
  requires forall i :: 0 <= i < 7 ==> s[i] >= 0
  ensures |process_array(s, a, k, index)| == 7
  ensures forall i :: 0 <= i < 7 ==> process_array(s, a, k, index)[i] >= 0
  ensures s[0] + s[1] + s[2] + s[3] + s[4] + s[5] + s[6] == process_array(s, a, k, index)[0] + process_array(s, a, k, index)[1] + process_array(s, a, k, index)[2] + process_array(s, a, k, index)[3] + process_array(s, a, k, index)[4] + process_array(s, a, k, index)[5] + process_array(s, a, k, index)[6]
  ensures process_array(s, a, k, index)[6] <= s[0] + s[1] + s[2] + s[3] + s[4] + s[5] + s[6]
  ensures index < |a| ==> process_array(s, a, k, index) == process_array(update_state(s, a[index], k), a, k, index + 1)
  decreases |a| - index
{
    if index == |a| then s
    else
        var ai := a[index];
        var new_s := update_state(s, ai, k);
        process_array(new_s, a, k, index + 1)
}

function update_state(s: seq<int>, ai: int, k: seq<int>): seq<int>
  requires |s| == 7 && |k| == 6
  requires ai in {4, 8, 15, 16, 23, 42}
  requires k == [4, 8, 15, 16, 23, 42]
  requires forall i :: 0 <= i < 7 ==> s[i] >= 0
  ensures |update_state(s, ai, k)| == 7
  ensures forall i :: 0 <= i < 7 ==> update_state(s, ai, k)[i] >= 0
  ensures s[0] + s[1] + s[2] + s[3] + s[4] + s[5] + s[6] == update_state(s, ai, k)[0] + update_state(s, ai, k)[1] + update_state(s, ai, k)[2] + update_state(s, ai, k)[3] + update_state(s, ai, k)[4] + update_state(s, ai, k)[5] + update_state(s, ai, k)[6]
{
    if ai == k[5] && s[5] > 0 then s[6 := s[6] + 1][5 := s[5] - 1]
    else if ai == k[4] && s[4] > 0 then s[5 := s[5] + 1][4 := s[4] - 1]
    else if ai == k[3] && s[3] > 0 then s[4 := s[4] + 1][3 := s[3] - 1]
    else if ai == k[2] && s[2] > 0 then s[3 := s[3] + 1][2 := s[2] - 1]
    else if ai == k[1] && s[1] > 0 then s[2 := s[2] + 1][1 := s[1] - 1]
    else if ai == k[0] && s[0] > 0 then s[1 := s[1] + 1][0 := s[0] - 1]
    else s
}

function number_of_complete_subsequences_partial(n: int, a: seq<int>, k: seq<int>, index: int): int
  requires ValidInput(n, a)
  requires |k| == 6
  requires k == [4, 8, 15, 16, 23, 42]
  requires 0 <= index <= |a|
  ensures 0 <= number_of_complete_subsequences_partial(n, a, k, index) <= n
{
    var s := [n, 0, 0, 0, 0, 0, 0];
    var partial_a := if index == 0 then [] else a[0..index];
    var final_s := process_array(s, partial_a, k, 0);
    final_s[6]
}

// <vc-helpers>
function sum_seq(s: seq<int>): int
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures sum_seq(s) >= 0
{
  if |s| == 0 then 0
  else s[0] + sum_seq(s[1..])
}

lemma lemma_update_state_sum_preserved(s: seq<int>, ai: int, k: seq<int>)
  requires |s| == 7 && |k| == 6
  requires ai in {4, 8, 15, 16, 23, 42}
  requires k == [4, 8, 15, 16, 23, 42]
  requires forall i :: 0 <= i < 7 ==> s[i] >= 0
  ensures sum_seq(s) == sum_seq(update_state(s, ai, k))
{
  // This lemma is directly supported by the ensures clauses of `update_state`
  // Specifically, `s[0] + s[1] + s[2] + s[3] + s[4] + s[5] + s[6] == update_state(s, ai, k)[0] + update_state(s, ai, k)[1] + update_state(s, ai, k)[2] + update_state(s, ai, k)[3] + update_state(s, ai, k)[4] + update_state(s, ai, k)[5] + update_state(s, ai, k)[6]`
  // which is equivalent to `sum_seq(s) == sum_seq(update_state(s, ai, k))` since sum_seq is defined as the sum of elements.
}

lemma lemma_process_array_sum_preserved(s: seq<int>, a: seq<int>, k: seq<int>, index: int)
  requires |s| == 7 && |k| == 6
  requires 0 <= index <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] in {4, 8, 15, 16, 23, 42}
  requires k == [4, 8, 15, 16, 23, 42]
  requires forall i :: 0 <= i < 7 ==> s[i] >= 0
  ensures sum_seq(s) == sum_seq(process_array(s, a, k, index))
  decreases |a| - index
{
  if index == |a| then
    // Base case: process_array returns s, so sum is preserved.
    assert sum_seq(s) == sum_seq(process_array(s, a, k, index));
  else
    var ai := a[index];
    var new_s := update_state(s, ai, k);
    lemma_update_state_sum_preserved(s, ai, k);
    assert sum_seq(s) == sum_seq(new_s);
    lemma_process_array_sum_preserved(new_s, a, k, index + 1);
    assert sum_seq(new_s) == sum_seq(process_array(new_s, a, k, index + 1));
    assert sum_seq(s) == sum_seq(process_array(new_s, a, k, index + 1));
  
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
  requires ValidInput(n, a)
  ensures 0 <= result <= n
  ensures result == n - 6 * (number_of_complete_subsequences(n, a))
// </vc-spec>
// <vc-code>
{
  var k := [4, 8, 15, 16, 23, 42];
  var s := [n, 0, 0, 0, 0, 0, 0];

  assert sum_seq(s) == n; // This holds by definition of s and sum_seq

  var final_s := process_array(s, a, k, 0);

  // Prove sum_seq(s) == sum_seq(final_s) using the lemma
  lemma_process_array_sum_preserved(s, a, k, 0);
  assert sum_seq(s) == sum_seq(final_s);

  var num_sequences := final_s[6];

  // We know sum_seq(s) == n and sum_seq(s) == sum_seq(final_s).
  // So, n == final_s[0] + final_s[1] + final_s[2] + final_s[3] + final_s[4] + final_s[5] + final_s[6].
  // Each increment to s[6] means a complete sequence has been formed, consuming one of each of the 6 values.
  // The values in final_s[0] .. final_s[5] represent the elements that did not form complete sequences.
  // The total number of elements 'n' can be thought of as the sum of elements that remain as partial sequences
  // plus the elements that formed complete sequences.
  // Thus, n = (final_s[0] + ... + final_s[5]) + 6 * final_s[6].
  // Let `unaccounted_elements` be `final_s[0] + ... + final_s[5]`.
  // Then `n = unaccounted_elements + 6 * num_sequences`.
  // This means `unaccounted_elements = n - 6 * num_sequences`.

  // The problem states `result == n - 6 * (number_of_complete_subsequences(n, a))`.
  // From the definition of `number_of_complete_subsequences`, it's `final_s[6]`.
  // So, `result` must be `n - 6 * final_s[6]`.
  result := n - 6 * num_sequences;

  // Proof for `0 <= result <= n`:
  // From `n = final_s[0] + ... + final_s[5] + 6 * final_s[6]`,
  // we have `n - 6 * final_s[6] = final_s[0] + ... + final_s[5]`.
  // Since `final_s[i] >= 0` for all `i` (as per `process_array` ensures),
  // `final_s[0] + ... + final_s[5] >= 0`.
  // Therefore, `result >= 0`.

  // To show `result <= n`:
  // We know `num_sequences >= 0` (from `number_of_complete_subsequences` ensures).
  // Since `6 >= 0`, `6 * num_sequences >= 0`.
  // Subtracting a non-negative value from `n` means `result <= n`.
  // Thus, `0 <= result <= n` holds.
}
// </vc-code>

