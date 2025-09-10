predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidOutput(result: seq<int>, input: string)
{
    |result| >= 0 &&
    (forall i :: 0 <= i < |result| ==> result[i] >= 1) &&
    (forall i :: 0 <= i < |result| ==> result[i] <= |result|)
}

// <vc-helpers>
function is_digit(c: char): bool
{
  '0' <= c <= '9'
}

function char_to_int(c: char): int
  requires is_digit(c)
{
  (c as int) - ('0' as int)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: seq<int>)
    requires ValidInput(input)
    ensures ValidOutput(result, input)
// </vc-spec>
// <vc-code>
{
    var digits_seq: seq<int> := [];
    var i := 0;
    while i < |input|
        invariant 0 <= i <= |input|
        invariant forall k :: 0 <= k < |digits_seq| ==> 1 <= digits_seq[k] <= |digits_seq| + 1 // Loosen upper bound temporarily
        invariant forall k :: 0 <= k < |digits_seq| ==> is_digit(input[k]) // Ensure input characters processed are digits
        invariant |digits_seq| == i // The number of processed digits matches the index
    {
        if is_digit(input[i]) {
            digits_seq := digits_seq + [char_to_int(input[i])];
        }
        i := i + 1;
    }

    // Now refine the upper bound for digits_seq elements
    // We want the result to follow 1 <= result[k] <= |result|
    // The current digits_seq has elements from 0 to 9. We need to filter and re-index.

    var final_result: seq<int> := [];
    var current_val := 1; // This will hold the next value to be assigned to the result sequence

    i := 0;
    while i < |digits_seq|
        invariant 0 <= i <= |digits_seq|
        invariant forall k :: 0 <= k < |final_result| ==> 1 <= final_result[k] <= |final_result|
        invariant current_val == |final_result| + 1
    {
        var digit_val := digits_seq[i];
        if digit_val >= 1 && digit_val <= current_val {
            // Need to carefully manage the insertion to ensure the monotonic property.
            // For this specific problem, values must be 1 to |result|.
            // The problem statement implies we're mapping input digits to positions.
            // If the input sequence is '123', the result should be [1,2,3].
            // If the input is '312', it implies a permutation or specific logic.
            // Given ValidOutput requirements:
            // (forall i :: 0 <= i < |result| ==> result[i] >= 1) &&
            // (forall i :: 0 <= i < |result| ==> result[i] <= |result|)
            // This is a common pattern for permutations or sequences like [1, 2, ..., N].
            // The simplest interpretation that fits the problem is to simply return a sequence
            // of increasing integers starting from 1, whose length is determined by the
            // number of digits in the input.

            // Let's re-interpret: The `ValidOutput` implies that the `result` is
            // a permutation of `[1, 2, ..., N]` where N = `|result|`.
            // The problem statement is "Given a Dafny file ... to generate code".
            // The previous setup attempts to parse digits, which might be a red herring
            // if the simplest valid output is required.

            // Let's assume the problem means to produce a sequence [1, 2, ..., N]
            // where N is the count of digits in the input.

            // The 'solve' method with 'input: string' suggests processing the input.
            // If the input is "abc123def", the output should be [1,2,3].
            // If input is "hello", output [].
            // If input is "101", output [1,2,1] or [1,2,3] with some permutation?

            // The problem statement is concise. The `ValidInput` and `ValidOutput`
            // predicates are fixed. `ValidOutput` is key: "result[i] <= |result|",
            // which smells like a permutation of `1..N`.

            // Let's re-evaluate the most straightforward interpretation:
            // Count the number of digits in `input`. Let this be `N`.
            // The `result` should be `[1, 2, ..., N]`.
            // This satisfies `ValidOutput` for all `N >= 0`.

            // If `result[i]` must be `1 <= result[i] <= |result|`, the simplest
            // sequence satisfying this for any non-zero length N is `[1, 2, ..., N]`.
            // The `input: string` implies the method should do *something* with the input.

            // Proposed interpretation:
            // 1. Count the number of numeric characters in `input`. Let this be `N`.
            // 2. Construct the sequence `[1, 2, ..., N]`.

            // This is arguably the simplest solution that makes `ValidOutput` hold
            // and uses parts of the `ValidInput` to derive `N`.

            final_result := final_result + [current_val];
            current_val := current_val + 1;
        }
        i := i + 1;
    }

    result := final_result;
}
// </vc-code>

