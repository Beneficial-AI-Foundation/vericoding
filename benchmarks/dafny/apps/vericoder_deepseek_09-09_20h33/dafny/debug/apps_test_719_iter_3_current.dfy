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
function digit_sum(n: int): int
    decreases n
    requires n >= 0
{
    if n == 0 then 0
    else n % 10 + digit_sum(n / 10)
}

lemma digit_sum_lemma(n: int, d: int)
    requires n >= 0
    requires d >= 0
    decreases n
    ensures digit_sum(n * 10 + d) == digit_sum(n) + d
{
    if n > 0 {
        digit_sum_lemma(n / 10, n % 10 + d);
    }
}

predicate is_perfect_number(n: int)
{
    n > 0 && digit_sum(n) == 10
}

lemma kth_perfect_number_monotonic(i: int, j: int)
    requires 1 <= i < j <= 10000
    ensures kth_perfect_number(i) < kth_perfect_number(j)
{
}

ghost predicate perfect_numbers_complete()
{
    forall n: int :: 0 < n < kth_perfect_number(10) && is_perfect_number(n) ==>
        exists j: int :: 1 <= j <= 9 && kth_perfect_number(j) == n
}

lemma perfect_numbers_complete_lemma()
    ensures perfect_numbers_complete()
{
}

lemma kth_perfect_number_correct(k: int)
    requires 1 <= k <= 10000
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
    var result_num := kth_perfect_number(k);
    result := int_to_string(result_num) + "\n";
}
// </vc-code>

