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

function abs_value_nat(n: nat): nat
    ensures abs_value_nat(n) == abs_value(n)
{
    n
}

lemma count_digits_nonnegative(n: nat)
    ensures count_digits(n) >= 1
    decreases n
{
    if n < 10 {
    } else {
        count_digits_nonnegative(n / 10);
    }
}

lemma count_even_odd_total(n: nat)
    ensures count_even_digits(n) + count_odd_digits(n) == count_digits(n)
    decreases n
{
    if n < 10 {
    } else {
        count_even_odd_total(n / 10);
    }
}

lemma abs_value_property(x: int)
    ensures abs_value(x) >= 0
    ensures x >= 0 ==> abs_value(x) == x
    ensures x < 0 ==> abs_value(x) == -x
{
}

lemma zero_digit_count()
    ensures count_digits(0) == 1
    ensures count_even_digits(0) == 1
    ensures count_odd_digits(0) == 0
{
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
    /* code modified by LLM (iteration 2): Handle num=0 case and verify postconditions */
    var abs_num := abs_value(num);
    
    even_count := 0;
    odd_count := 0;
    
    count_digits_nonnegative(abs_num);
    count_even_odd_total(abs_num);
    zero_digit_count();
    
    if abs_num == 0 {
        even_count := 1;
        odd_count := 0;
    } else {
        even_count := count_even_digits(abs_num);
        odd_count := count_odd_digits(abs_num);
    }
}
// </vc-code>
