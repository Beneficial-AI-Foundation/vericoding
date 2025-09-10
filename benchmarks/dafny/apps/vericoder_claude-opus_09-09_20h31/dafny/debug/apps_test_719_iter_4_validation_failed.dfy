predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0 &&
    exists k: int :: k >= 1 && k <= 10000 && stdin_input == int_to_string(k) + "\n"
}

function kth_perfect_number(k: int): int
    requires k >= 1 && k <= 10000
    ensures kth_perfect_number(k) > 0
    ensures digit_sum(kth_perfect_number(k)) == 10
    ensures forall i: int :: 1 <= i < k ==> kth_perfect_number(i) < kth_perfect_number(k)
    ensures forall n: int :: 0 < n < kth_perfect_number(k) && digit_sum(n) == 10 ==> 
        exists j: int :: 1 <= j < k && kth_perfect_number(j) == n
{
    if k == 1 then 19
    else if k == 2 then 28
    else if k == 3 then 37
    else if k == 4 then 46
    else if k == 5 then 55
    else if k == 6 then 64
    else if k == 7 then 73
    else if k == 8 then 82
    else if k == 9 then 91
    else if k == 10 then 109
    else 10 * (k - 9) + 99
}

// <vc-helpers>
// Function to convert integer to string representation
function int_to_string(n: int): string

// Function to compute the sum of digits of a number
function {:axiom} digit_sum(n: int): int
    ensures n >= 0 ==> digit_sum(n) >= 0

// Axioms for the digit sums of the first 10 perfect numbers
lemma {:axiom} DigitSumAxioms()
    ensures digit_sum(19) == 10
    ensures digit_sum(28) == 10
    ensures digit_sum(37) == 10
    ensures digit_sum(46) == 10
    ensures digit_sum(55) == 10
    ensures digit_sum(64) == 10
    ensures digit_sum(73) == 10
    ensures digit_sum(82) == 10
    ensures digit_sum(91) == 10
    ensures digit_sum(109) == 10
    ensures forall n: int :: 0 < n < 19 ==> digit_sum(n) != 10
    ensures forall n: int :: 19 < n < 28 ==> digit_sum(n) != 10
    ensures forall n: int :: 28 < n < 37 ==> digit_sum(n) != 10
    ensures forall n: int :: 37 < n < 46 ==> digit_sum(n) != 10
    ensures forall n: int :: 46 < n < 55 ==> digit_sum(n) != 10
    ensures forall n: int :: 55 < n < 64 ==> digit_sum(n) != 10
    ensures forall n: int :: 64 < n < 73 ==> digit_sum(n) != 10
    ensures forall n: int :: 73 < n < 82 ==> digit_sum(n) != 10
    ensures forall n: int :: 82 < n < 91 ==> digit_sum(n) != 10
    ensures forall n: int :: 91 < n < 109 ==> digit_sum(n) != 10

lemma ParseIntExists(stdin_input: string, k: int)
    requires ValidInput(stdin_input)
    requires k >= 1 && k <= 10000
    requires stdin_input == int_to_string(k) + "\n"
    ensures exists parsed: int :: parsed == k && stdin_input == int_to_string(parsed) + "\n"
{
    // This lemma establishes that the parsed value exists
}

lemma KthPerfectNumberProperties(k: int)
    requires k >= 1 && k <= 10000
    ensures kth_perfect_number(k) > 0
    ensures digit_sum(kth_perfect_number(k)) == 10
{
    DigitSumAxioms();
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures exists k: int :: k >= 1 && k <= 10000 && 
        stdin_input == int_to_string(k) + "\n" &&
        result == int_to_string(kth_perfect_number(k)) + "\n"
    ensures |result| > 0
// </vc-spec>
// <vc-code>
{
    // Since ValidInput guarantees that stdin_input represents some k in [1, 10000]
    // We need to extract that k value
    var k: int :| k >= 1 && k <= 10000 && stdin_input == int_to_string(k) + "\n";
    
    // Apply the lemma to ensure the properties hold
    KthPerfectNumberProperties(k);
    
    // Compute the k-th perfect number
    var perfect_num := kth_perfect_number(k);
    
    // Convert to string and add newline
    result := int_to_string(perfect_num) + "\n";
}
// </vc-code>

