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
/* helper modified by LLM (iteration 4): Add lemma to prove sum of even and odd digits equals total digits */
lemma count_digits_sum_lemma(n: nat)
    requires n >= 0
    ensures count_even_digits(n) + count_odd_digits(n) == count_digits(n)
{
    if n < 10 {
        // Base case, n is a single digit
        if is_even_digit(n) {
            calc {
                count_even_digits(n) + count_odd_digits(n);
                1 + 0;
                1;
                count_digits(n);
            }
        } else {
            calc {
                count_even_digits(n) + count_odd_digits(n);
                0 + 1;
                1;
                count_digits(n);
            }
        }
    } else {
        // Recursive step
        var last_digit := n % 10;
        var remaining_digits := n / 10;
        count_digits_sum_lemma(remaining_digits);
        calc {
            count_even_digits(n) + count_odd_digits(n);
            (if is_even_digit(last_digit) then 1 else 0) + count_even_digits(remaining_digits) +
            (if !is_even_digit(last_digit) then 1 else 0) + count_odd_digits(remaining_digits);
            (if is_even_digit(last_digit) then 1 else 0) +
            (if !is_even_digit(last_digit) then 1 else 0) +
            (count_even_digits(remaining_digits) + count_odd_digits(remaining_digits));
            1 + count_digits(remaining_digits);
            count_digits(n);
        }
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
/* code modified by LLM (iteration 4): Call helper lemma to satisfy postcondition regarding count_digits */
{
    var abs_num := abs_value(num);

    if num == 0 {
        even_count := 1;
        odd_count := 0;
    } else {
        even_count := count_even_digits(abs_num);
        odd_count := count_odd_digits(abs_num);
        count_digits_sum_lemma(abs_num);
    }
}
// </vc-code>
