function concat_seqs(seqs: seq<seq<char>>): seq<char>
{
    if |seqs| == 0 then []
    else seqs[0] + concat_seqs(seqs[1..])
}

predicate ValidSplit(result: seq<seq<char>>, k: int, q: seq<char>)
{
    |result| == k &&
    (forall i :: 0 <= i < |result| ==> |result[i]| > 0) &&
    (forall i, j :: 0 <= i < j < |result| ==> result[i][0] != result[j][0]) &&
    concat_seqs(result) == q
}

// <vc-helpers>
function find_first_occurrence(s: seq<char>, c: char): int
  reads s
  ensures find_first_occurrence(s, c) == -1 <==> c !in s
  ensures 0 <= find_first_occurrence(s, c) < |s| ==> s[find_first_occurrence(s, c)] == c
  ensures forall i :: 0 <= i < find_first_occurrence(s, c) ==> s[i] != c
{
  if |s| == 0 then -1
  else if s[0] == c then 0
  else
    var rest_idx := find_first_occurrence(s[1..], c);
    if rest_idx == -1 then -1
    else 1 + rest_idx
}

function sub_seq_until(s: seq<char>, c: char): seq<char>
  reads s
  ensures forall i :: 0 <= i < |sub_seq_until(s, c)> ==> s[i] == sub_seq_until(s, c)[i]
  ensures (c in s) ==> sub_seq_until(s, c) == s[..find_first_occurrence(s, c)]
  ensures !(c in s) ==> sub_seq_until(s, c) == s
{
  var idx := find_first_occurrence(s, c);
  if idx == -1 then s
  else s[..idx]
}

function sub_seq_after(s: seq<char>, c: char): seq<char>
  reads s
  ensures (c in s) ==> sub_seq_after(s, c) == s[find_first_occurrence(s, c)..]
  ensures !(c in s) ==> sub_seq_after(s, c) == []
{
  var idx := find_first_occurrence(s, c);
  if idx == -1 then []
  else s[idx..]
}

lemma lemma_concat_seqs_append(s1: seq<char>, s2: seq<char>)
  ensures concat_seqs([s1, s2]) == s1 + s2
{}

lemma lemma_concat_seqs_split(s: seq<seq<char>>, i: int)
  requires 0 <= i <= |s|
  ensures concat_seqs(s) == concat_seqs(s[..i]) + concat_seqs(s[i..])
{}

lemma lemma_concat_seqs_singleton(s: seq<char>)
  ensures concat_seqs([s]) == s
{}

lemma lemma_ValidSplit_properties(result: seq<seq<char>>, k: int, q: seq<char>)
  requires ValidSplit(result, k, q)
  ensures k > 0 ==> |result| == k
  ensures k > 0 ==> (forall i :: 0 <= i < |result| ==> |result[i]| > 0)
  ensures k > 0 ==> (forall i, j :: 0 <= i < j < |result| ==> result[i][0] != result[j][0])
  ensures k > 0 ==> concat_seqs(result) == q
{}

lemma lemma_NoDuplicateFirstChars(s: seq<seq<char>>)
  requires (forall i :: 0 <= i < |s| ==> |s[i]| > 0)
  requires (forall i, j :: 0 <= i < j < |s| ==> s[i][0] != s[j][0])
  ensures forall i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i][0] != s[j][0]
{}
// </vc-helpers>

// <vc-spec>
method solve(k: int, q: seq<char>) returns (result: seq<seq<char>>)
    requires k >= 0
    requires |q| >= 0
    ensures k <= 0 || |q| == 0 ==> |result| == 0
    ensures k > 0 && |q| > 0 ==> (
        (|result| == 0) || ValidSplit(result, k, q)
    )
// </vc-spec>
// <vc-code>
{
    if k <= 0 || |q| == 0 then
        return [];
    else if k == 1 then
        return [[q[0]]]; // This is a heuristic. The problem doesn't state how to determine the split.
    else
    {
        var used_chars: set<char> := {};
        var current_q := q;
        var res_seq: seq<seq<char>> := [];

        while k > 0 && |current_q| > 0 {
            // Find the first character in current_q that hasn't been used yet.
            var first_char: char := '.'; // Placeholder, will be reassigned.
            var first_char_idx: int := -1;

            for i := 0 to |current_q| - 1 {
                if !(current_q[i] in used_chars) {
                    first_char := current_q[i];
                    first_char_idx := i;
                    break;
                }
            }

            if first_char_idx == -1 {
                // All characters in current_q have been used as first chars.
                // This means we cannot find 'k' distinct first characters.
                // Or we have consumed some from current_q but can't find 'k' total splits.
                return [];
            }

            // We need to find the segment starting with current_q[first_char_idx]
            // We assume that the problem intends for us to find *distinct* initial characters.
            // A simple greedy approach: Take the first character, and then the rest of the string until
            // we find another character that might be a *different* first character in a subsequent segment.
            // The problem statement is underspecified for a unique solution without more constraints.
            // Using a simple split strategy here: each segment is just its first character.

            // Given the ValidSplit predicate: (forall i :: 0 <= i < |result| ==> |result[i]| > 0)
            // And (forall i, j :: 0 <= i < j < |result| ==> result[i][0] != result[j][0])
            // And concat_seqs(result) == q

            // Let's try to construct `result` greedily.
            // The constraint `concat_seqs(result) == q` implies that we must use up all of `q`.
            // The constraint `|result| == k` implies we must have `k` terms.
            // The constraint `forall i :: 0 <= i < |result| ==> |result[i]| > 0` implies each term is non-empty.
            // The constraint `forall i, j :: 0 <= i < j < |result| ==> result[i][0] != result[j][0]` implies distinct first characters.

            // A more robust greedy strategy:
            // Find the first available character in `current_q` that is not in `used_chars`.
            // This character `c` will be the starting character of the next segment.
            var current_segment_first_char := current_q[first_char_idx];
            used_chars := used_chars + {current_segment_first_char};

            // Now, we need to extract a segment `s` such that `s[0] == current_segment_first_char`
            // and `s` is part of `current_q`, and `concat_seqs(res_seq + [s] + remaining_splits) == q`.
            // The simplest strategy to ensure `concat_seqs` holds is to make the last segment absorb everything remaining.
            // But we need `k` segments with distinct first chars.

            // Let's process `q` from left to right.
            // If we need `k` segments, we try to form these segments.
            // Each segment must start with a character not seen before.

        }

        // Reset for a more direct greedy approach that satisfies all conditions.
        // The core idea is to find `k` distinct first characters in `q`.
        // If we can't find `k` distinct first characters, or `q` is too short, return [].
        // If we can, partition `q` using these characters.

        if k > 0 && |q| > 0 {
            var temp_result: seq<seq<char>> := [];
            var remaining_q := q;
            var current_k := k;
            var distinct_first_chars: set<char> := {};

            while current_k > 1 {
                // Find the first character in remaining_q that has not been used as a first character
                var segment_start_idx := -1;
                for i := 0 to |remaining_q| - 1 {
                    if !(remaining_q[i] in distinct_first_chars) {
                        segment_start_idx := i;
                        break;
                    }
                }

                if segment_start_idx == -1 {
                    // No new distinct first character found for this segment, cannot make k distinct segments
                    return [];
                }

                var first_char_for_this_segment := remaining_q[segment_start_idx];
                distinct_first_chars := distinct_first_chars + {first_char_for_this_segment};

                // Form the segment. This is the trickiest part given the constraints.
                // The most straightforward way to ensure `concat_seqs(result) == q` is if
                // `result` is a partition of `q`.
                // We need to cut `remaining_q` into a piece for `temp_result` and a new `remaining_q`.
                // Where do we make the cut? At the next character that is *not* `first_char_for_this_segment`
                // and potentially could be the start of a new segment.
                // A simpler approach: cut after the first character if it guarantees distinctness.
                // This will simplify the problem, but might not be the intent for `|result[i]| > 0`.

                // Let's try to find the next distinct character to make the split.
                var next_distinct_char_idx := -1;
                for i := segment_start_idx + 1 to |remaining_q| - 1 {
                    if !(remaining_q[i] in distinct_first_chars) { // It's distinct and haven't used yet
                        next_distinct_char_idx := i;
                        break;
                    }
                }

                var current_segment: seq<char>;
                if next_distinct_char_idx != -1 {
                    current_segment := remaining_q[..next_distinct_char_idx];
                } else {
                    // If no more distinct characters for future segments, this segment takes up to the
                    // end of remaining_q (if it's the last one). This case is for current_k == 1.
                    // But we are in current_k > 1 loop. So, if we can't find a next distinct character,
                    // we cannot fulfill the k distinct segments.
                    // So, if next_distinct_char_idx is -1 within this loop, we return [].
                    return [];
                }
                
                assert |current_segment| > 0; // The segment must be non-empty

                temp_result := temp_result + [current_segment];
                remaining_q := remaining_q[next_distinct_char_idx..];
                current_k := current_k - 1;
            }

            // After the loop, current_k should be 1. The last segment takes all remaining_q.
            if current_k == 1 {
                if |remaining_q| > 0 {
                    // Check if the first character of remaining_q is distinct.
                    // It MUST be distinct from previous `distinct_first_chars` IF `k > 0`.
                    // But our loop only adds current_q[segment_start_idx] to distinct_first_chars IF it was distinct.
                    // And this current `remaining_q[0]` would have been checked.
                    // The problem is that the `next_distinct_char_idx` might have picked a character
                    // that was *already* in `distinct_first_chars` (since the condition was if it's not
                    // in `distinct_first_chars` for that iteration).

                    // Let's simplify the strategy (this is where the problem is underspecified,
                    // any valid split that satisfies the conditions would be fine).
                    // We need `k` parts. Each part must start with a distinct character.
                    // All parts together must form `q`.
                    // What if we try to find `k` distinct characters in `q` greedily, and then try to split it?

                    // A minimal approach might be to assign each distinct character to a segment of length 1,
                    // and then lump the rest into the last segment, if possible.
                    // But this might fail `|result[i]| > 0` for intermediate segments.

                    // Let's try this: Take the first `k-1` unique characters found in `q` as segment beginnings.
                    // For each, form a segment up to the next such unique character.
                    // The last segment takes the rest.

                    var actual_result: seq<seq<char>> := [];
                    var current_index := 0;
                    var found_first_chars: set<char> := {};

                    for i := 0 to k - 2 { // Find k-1 segments
                        if current_index >= |q| { return []; } // Not enough characters in q

                        var seg_start_char := q[current_index];

                        // Ensure this character hasn't been used as a first char
                        // This implies we need to skip characters that have been seen
                        while current_index < |q| && q[current_index] in found_first_chars {
                             current_index := current_index + 1;
                        }
                        if current_index >= |q| { return []; } // Ran out of q looking for a distinct char
                        seg_start_char := q[current_index];
                        found_first_chars := found_first_chars + {seg_start_char};

                        var next_distinct_char_index := -1;
                        for j := current_index + 1 to |q| - 1 {
                            // Find the 'next' distinct character that could start a new segment
                            if !(q[j] in found_first_chars) {
                                next_distinct_char_index := j;
                                break;
                            }
                        }

                        if next_distinct_char_index == -1 {
                            // Cannot find k distinct characters. Or no more distinct chars for next segments.
                            // So this current segment must be the last one, meaning k must be 1.
                            // But we are in a loop for k-1 segments, so this is failure.
                            return [];
                        }

                        var segment_val := q[current_index .. next_distinct_char_index];
                        assert |segment_val| > 0;
                        actual_result := actual_result + [segment_val];
                        current_index := next_distinct_char_index;
                    }

                    // The last segment
                    if current_index < |q| {
                        var last_segment := q[current_index..];
                        if |last_segment| > 0 {
                            // Check if the first char of the last segment is distinct from previous
                            if last_segment[0] in found_first_chars {
                                // This means we could not find k distinct characters.
                                return [];
                            }
                            actual_result := actual_result + [last_segment];
                        } else {
                            // The last segment is empty, which violates |result[i]| > 0
                            return [];
                        }
                    } else {
                        // q was fully consumed by earlier segments, making the last segment empty.
                        return [];
                    }

                    // Check if we have exactly k segments
                    if |actual_result| == k {
                        // Final check of ValidSplit against actual_result, q, k
                        // (This check is for reasoning, not actual code execution that solves problem)
                        // This solution assumes that finding k distinct characters greedily and making splits
                        // at these points (or before the next distinct one) is the intended logic.
                        // However, multiple valid splits might exist. The problem asks for *a* verified solution.
                        
                        // Let's attempt to verify the properties for `actual_result`
                        // |result| == k: Checked above.
                        // (forall i :: 0 <= i < |result| ==> |result[i]| > 0): Ensured by segment construction.
                        // (forall i, j :: 0 <= i < j < |result| ==> result[i][0] != result[j][0]): Ensured by `found_first_chars` tracking.
                        // concat_seqs(result) == q: Ensured by partitioning `q`.
                        return actual_result;
                    } else {
                        return [];
                    }

                } else {
                    return []; // q is empty but k > 0, cannot find k segments with distinct first chars.
                }
            } else {
                return []; // current_k is not 1, meaning we ended early or have incorrect k.
            }
        }
        return [];
    }
}
// </vc-code>

