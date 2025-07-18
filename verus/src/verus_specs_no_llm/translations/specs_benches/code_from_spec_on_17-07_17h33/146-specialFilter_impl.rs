//ATOM
function extract_first_digit_spec(n: int): int
    decreases if n >= 0 then n else -n
{
    if n < 10 then n else extract_first_digit_spec(n / 10)
}

//IMPL extract_first_digit
/* code modified by LLM (iteration 2): Fixed type compatibility and added proper verification */
method extract_first_digit(n: nat) returns (res: nat)
    decreases n
    ensures res == extract_first_digit_spec(n)
{
    if n < 10 {
        res := n;
    } else {
        res := extract_first_digit(n / 10);
    }
}

//ATOM
function extract_last_digit_spec(n: int): int
{
    n % 10
}

//IMPL extract_last_digit
/* code modified by LLM (iteration 2): Fixed return type to match spec */
method extract_last_digit(n: nat) returns (res: nat)
    ensures res == extract_last_digit_spec(n)
{
    res := n % 10;
}

//ATOM
predicate is_odd(n: int)
{
    (n % 2) != 0
}

//ATOM
predicate is_valid_element_spec(n: int)
{
    n > 10 && is_odd(extract_first_digit_spec(n)) && is_odd(extract_last_digit_spec(n))
}

//IMPL is_valid_element
/* code modified by LLM (iteration 2): Fixed type compatibility and added proper verification */
method is_valid_element(n: int) returns (res: bool)
    ensures res == is_valid_element_spec(n)
{
    if n > 10 {
        var first_digit := extract_first_digit(n as nat);
        var last_digit := extract_last_digit(n as nat);
        res := (first_digit % 2 != 0) && (last_digit % 2 != 0);
    } else {
        res := false;
    }
}

//ATOM
function special_filter_spec(seq: seq<int>): int
    decreases |seq|
{
    if |seq| == 0 then 0
    else special_filter_spec(seq[..|seq|-1]) + (if is_valid_element_spec(seq[|seq|-1]) then 1 else 0)
}

//IMPL special_filter
/* code modified by LLM (iteration 2): Added helper lemma and proper verification */
method special_filter(numbers: seq<int>) returns (count: nat)
    ensures count == special_filter_spec(numbers)
{
    count := 0;
    var i := 0;
    
    /* code modified by LLM (iteration 2): Added lemma to help with verification */
    lemma_special_filter_prefix(numbers, 0);
    
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant count == special_filter_spec(numbers[..i])
    {
        var is_valid := is_valid_element(numbers[i]);
        if is_valid {
            count := count + 1;
        }
        i := i + 1;
        
        /* code modified by LLM (iteration 2): Added lemma call to maintain invariant */
        lemma_special_filter_extend(numbers, i);
    }
}

/* code modified by LLM (iteration 2): Added helper lemma for base case */
lemma lemma_special_filter_prefix(numbers: seq<int>, i: nat)
    requires i == 0
    ensures special_filter_spec(numbers[..i]) == 0
{
    assert numbers[..0] == [];
}

/* code modified by LLM (iteration 2): Added helper lemma for inductive step */
lemma lemma_special_filter_extend(numbers: seq<int>, i: nat)
    requires 0 < i <= |numbers|
    ensures special_filter_spec(numbers[..i]) == 
            special_filter_spec(numbers[..i-1]) + (if is_valid_element_spec(numbers[i-1]) then 1 else 0)
{
    assert numbers[..i] == numbers[..i-1] + [numbers[i-1]];
}