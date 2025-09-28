// <vc-preamble>

function abs_value(x: int): int
{
    if x < 0 then -x else x
}

function count_digits(n: nat): nat
    requires n >= 0
{
    if n < 10 then 1 else 1 + count_digits(n / 10)
}

function is_even_digit(d: nat): bool
    requires d < 10
{
    d % 2 == 0
}

function count_even_digits(n: nat): nat
    requires n >= 0
    decreases n
{
    if n < 10 then
        if is_even_digit(n) then 1 else 0
    else
        (if is_even_digit(n % 10) then 1 else 0) + count_even_digits(n / 10)
}

function count_odd_digits(n: nat): nat
    requires n >= 0
    decreases n
{
    if n < 10 then
        if !is_even_digit(n) then 1 else 0
    else
        (if !is_even_digit(n % 10) then 1 else 0) + count_odd_digits(n / 10)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove that even and odd digit counts sum to total digit count */
lemma even_odd_sum_equals_total(n: nat)
    requires n >= 0
    ensures count_even_digits(n) + count_odd_digits(n) == count_digits(n)
    decreases n
{
    if n < 10 {
        // Base case: single digit
        if is_even_digit(n) {
            assert count_even_digits(n) == 1;
            assert count_odd_digits(n) == 0;
            assert count_digits(n) == 1;
        } else {
            assert count_even_digits(n) == 0;
            assert count_odd_digits(n) == 1;
            assert count_digits(n) == 1;
        }
    } else {
        // Recursive case
        even_odd_sum_equals_total(n / 10);
    }
}
// </vc-helpers>

// <vc-spec>
method even_odd_count(num: int) returns (even_count: int, odd_count: int)
    ensures even_count >= 0 && odd_count >= 0
    ensures even_count + odd_count >= 1
    ensures var abs_num := abs_value(num);
            even_count == count_even_digits(abs_num) &&
            odd_count == count_odd_digits(abs_num)
    ensures even_count + odd_count == count_digits(abs_value(num))
    ensures num == 0 ==> (even_count == 1 && odd_count == 0)
    ensures abs_value(num) == abs_value(-num) ==> 
            (even_count == count_even_digits(abs_value(-num)) && 
             odd_count == count_odd_digits(abs_value(-num)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added lemma call to prove postcondition */
    var abs_num := abs_value(num);
    even_odd_sum_equals_total(abs_num);
    even_count := count_even_digits(abs_num);
    odd_count := count_odd_digits(abs_num);
}
// </vc-code>
