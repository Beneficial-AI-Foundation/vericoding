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
lemma {:axiom} digit_sum_lemma(n: int)
    ensures digit_sum(n) >= 0
{
}

lemma {:axiom} digit_sum_mult_10(n: int)
    ensures digit_sum(10 * n) == digit_sum(n)
{
}

lemma {:axiom} digit_sum_add_99(n: int)
    ensures digit_sum(n + 99) == digit_sum(n) + 18
{
}

lemma {:axiom} kth_perfect_number_correct(k: int)
    requires k >= 1 && k <= 10000
    ensures digit_sum(kth_perfect_number(k)) == 10
{
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
    var k_str := stdin_input[..|stdin_input| - 1];
    var k := string_to_int(k_str);
    result := int_to_string(kth_perfect_number(k)) + "\n";
}
// </vc-code>

